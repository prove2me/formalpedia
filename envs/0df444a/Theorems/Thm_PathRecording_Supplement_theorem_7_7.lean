-- Prove2me | Theorems.Thm_PathRecording_Supplement_theorem_7_7
-- name    : PathRecording.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:34:46.044504+00:00
-- url     : https://prove2.me/theorems/839a2a33-d1b0-4997-93ef-2d6641aba8ab
-- title:
--   Theorem 7.7 — a unitary 2-design maps any state into $\mathrm{DNP}_{N,t}$: $\mathbb E_C\,\mathrm{Tr}[\Pi_{\mathrm{DNP}}C^{\otimes t}\rho(C^\dagger)^{\otimes t}]\ge1-6t^2/(N-t+1)$
-- statement:
--   Let $1\le t\le N$, let $\Pi_{\mathrm{DNP}_{N,t}}$ be the orthogonal projection onto the distinct nonplussed subspace $\mathrm{DNP}_{N,t}=\mathrm{Dist}_{N,t}\cap\mathrm{NoPlus}_{N,t}$ of $(\mathbb C^N)^{\otimes t}$, and let $C$ be drawn from any exact unitary 2-design on $\mathbb C^N$, that is, from a probability measure on $U(N)$ whose second moments agree with those of the Haar measure. Then for every state $\rho$ on $(\mathbb C^N)^{\otimes t}$,
--   $$\mathbb E_C\Big[\mathrm{Tr}\big(\Pi_{\mathrm{DNP}_{N,t}}\,C^{\otimes t}\rho\,(C^\dagger)^{\otimes t}\big)\Big]\;\ge\;1-\frac{6t^2}{N-t+1}.$$
--   This is the explicit form, Eq. (7.59), of the printed bound $1-O(t^2/N)$ (7.16).
--
--   A random 2-design therefore sends almost all of any adversary's query state into the subspace on which the path-recording oracles of $U(N)$ and $S_N$ nearly agree; this is the first step of the proof that a random permutation composed with a 2-design is pseudorandom.
--
--   **Formalization Note** $\Pi_{\mathrm{DNP}_{N,t}}$ is the published projector `PRUPermLayer.projMat` onto the published `PRUPermLayer.dnpSub` (the intersection of the span of the $|\vec x\rangle$ with distinct entries and the range of $(I-|+\rangle\langle+|)^{\otimes t}$). $C^{\otimes t}$ acts on the product basis $|\vec x\rangle$; the design condition is the published `RandomGateDesign.MasterBound.IsExactDesign` for $t=2$ against a Haar probability measure `IsHaarProb` on $U(N)$.
--
--   Differences from the source:
--   - generalization: E_C Tr[Π_DNP C^{⊗t} ρ (C†)^{⊗t}] ≥ 1 − O(t²/N) (7.16) → the explicit bound ≥ 1 − 6t²/(N − t + 1); reason: (7.59) is the constant the proof produces; under the section's t ≤ c√N with c ≤ 1/2, N − t + 1 ≥ N/2, so it gives (7.16) with O-constant 12
--   - generalization: Section 7's standing assumption t ≤ c√N for a sufficiently small absolute constant c (p.96) → every 1 ≤ t ≤ N; reason: the proof (pp.97–105) does not use it; where Lemma 7.15's rearrangement needs N − 2t + 2 > 0, the bound is trivial otherwise, since then 6t²/(N − t + 1) > 1; 1 ≤ t ≤ N is the range on which Dist_{N,t} is defined (Definition 6.2)
--   - reading: C any unitary 2-design on ℂᴺ → C drawn from an exact unitary 2-design: a probability measure D on U(N) whose mixed second moment ∫ C^{⊗2}⊗conj(C)^{⊗2} dD equals that of a Haar probability measure μ (published RandomGateDesign.MasterBound.IsExactDesign μ D 2 with IsHaarProb μ); reason: the paper does not define the term; the proof uses the exact second and first moments (Lemmas 7.1, 7.3), and Corollary 7.35 says 'exact unitary 2-design'; equality of mixed moments is equality of the twirls E_C[C^{⊗2}X(C†)^{⊗2}]
--   - encoding: any state ρ on (ℂᴺ)^{⊗t} and the expectation E_C of a trace → a positive semidefinite matrix of trace 1 on the product basis Fin t → Fin N, and the D-integral of the real part of the trace; reason: the trace is real since Π_DNP and the conjugated state are positive semidefinite
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 7.7, Eq. (7.16), p.99; explicit constant Eq. (7.59), proof pp.104–105; Definitions 6.2–6.3, p.77, 7.2, p.97, 7.5, p.98

import Mathlib
import Definitions.Def_PRUPermLayer_dnpSub
import Definitions.Def_PRUPermLayer_projMat
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_RandomGateDesign_MasterBound_Moments

set_option autoImplicit false

namespace PathRecording.Supplement

open Matrix MeasureTheory
open scoped ComplexOrder

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 7.7, Eq. (7.16), p.99, with the explicit constant of its proof,
Eq. (7.59), p.105: let `Π_{DNP_{N,t}}` be the projection onto the distinct nonplussed subspace and
let `C` be drawn from any exact unitary 2-design on `ℂᴺ`. Then for every state `ρ` on `(ℂᴺ)^{⊗t}`,
`E_C Tr[Π_{DNP_{N,t}} C^{⊗t} ρ (C†)^{⊗t}] ≥ 1 − 6t²/(N − t + 1)`, for all `1 ≤ t ≤ N`.

**Formalization Note.**
* `Π_{DNP_{N,t}}` is the published `PRUPermLayer.projMat (PRUPermLayer.dnpSub N t)`: the matrix of the
  orthogonal projection onto `Dist_{N,t} ∩ NoPlus_{N,t}` (Definitions 6.3, 7.2, 7.5), with
  `Dist_{N,t}` spanned by the `|x⃗⟩` with injective `x⃗`, and `NoPlus_{N,t}` the range of
  `(I − |+⟩⟨+|)^{⊗t}`, `|+⟩⟨+|` the matrix with all entries `1/N`. It is the projection onto the
  intersection, not the product `Π_Dist Π_NoPlus`.
* A unitary 2-design is a probability measure `D` on `U(N)` whose second mixed moment
  `∫ C^{⊗2} ⊗ \overline{C}^{⊗2} dD(C)` equals that of a Haar probability measure `μ` on `U(N)`: the
  published `RandomGateDesign.MasterBound.IsExactDesign μ D 2` with
  `RandomGateDesign.MasterBound.IsHaarProb μ` (probability, left- and right-invariant). Equality of
  the mixed second moments is equality of the twirls `E_C[C^{⊗2} X (C†)^{⊗2}]` for every `X`.
* A state is a positive semidefinite matrix of trace `1` on the product basis `Fin t → Fin N`.
  `C^{⊗t}` is the published matrix tensor power. The trace is real; its real part is integrated.
* The printed bound is `1 − O(t²/N)`; the constant is the one the proof produces in (7.59). The
  section's standing assumption `t ≤ c√N` is not used by this proof and is not imposed. -/
theorem theorem_7_7 (N t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N)
    (μ D : Measure (RandomGateDesign.MasterBound.U N))
    (hμ : RandomGateDesign.MasterBound.IsHaarProb μ)
    (hD : RandomGateDesign.MasterBound.IsExactDesign μ D 2)
    (ρ : Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ) (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) :
    1 - 6 * (t : ℝ) ^ 2 / ((N : ℝ) - t + 1) ≤
      ∫ C, (Matrix.trace (PRUPermLayer.projMat (PRUPermLayer.dnpSub N t) *
          WildeQIT.Schumacher.tensorPow t (C : Matrix (Fin N) (Fin N) ℂ) * ρ *
          (WildeQIT.Schumacher.tensorPow t (C : Matrix (Fin N) (Fin N) ℂ))ᴴ)).re ∂D := by sorry

end PathRecording.Supplement
