-- Prove2me | Theorems.Thm_QubitTracking_theorem_6_2
-- name    : QubitTracking.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:51.165956+00:00
-- url     : https://prove2.me/theorems/b2a73581-144a-4fca-84dd-73c357a8041a
-- title:
--   Theorem 6.2 ([KY25] Theorem 5.4) — coset monogamy: $\Pr[\text{win}]\le 1/2+\mathrm{negl}(\lambda)$
-- statement:
--   Let $A\le\mathbb F_2^n$ be spanned by the first $n/2$ columns of a uniformly random change of basis $U$, $s$ uniform in $\mathsf{CS}(A)$, $t$ uniform in $\mathsf{CS}(A^\perp)$, and $|A_{s,t}\rangle=|A|^{-1/2}\sum_{a\in A}(-1)^{\langle a,t\rangle}|a+s\rangle$. In the coset monogamy game, $\mathcal A_M$ receives $|A_{s,t}\rangle$ and splits it into $\mathbf L\mathbf R$; $\mathcal A_L$ receives $(U,r_L)$ and returns $b^l_0$, $\mathcal A_R$ receives $(U,r_R)$ and returns $b^r_1$, for uniform $r_L,r_R\in\mathbb F_2^n$; the adversary wins iff $b^l_0\oplus b^r_1=\langle r_L,s\rangle\oplus\langle r_R,t\rangle$. For every adversary,
--   $$\Pr[\mathsf{CosetMonogamy}(\mathcal A,1^\lambda)=1]\le\frac12+\mathrm{negl}(\lambda).$$
--
--   It is the base monogamy game from which §6 builds the multi-stage games.
--
--   Differences from the source:
--   - reading: n (unspecified dependence on λ) → n = n(λ) even, polynomially bounded and ≥ λ; reason: the setting of §6 (Definition 6.1, p.32: n(λ) ≥ λ, polynomials); n/2 must be an integer
--   - encoding: any adversary (𝒜_M, 𝒜_L, 𝒜_R) → any finite registers 𝐋, 𝐑, any isometry 𝐌 → 𝐋𝐑 and any two-outcome measurements depending on (U, r); reason: a channel is an isometry with a discarded environment the adversary may hand to 𝒜_L; outputs are bits
--   - reading: 'for any adversary, ≤ 1/2 + negl(λ)' → one negligible function bounding every adversary; reason: adversaries are unbounded, so the bound is uniform over them; this is the stronger reading
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 6.2 and Remark 6.3, pp.33–34

import Definitions.Def_QubitTracking_cosetWinProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false

namespace QubitTracking

/-- **Theorem 6.2** ([KY25] Theorem 5.4; Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits
Through Space and Time*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 6.2,
pp.33–34, with the canonical representatives of Remark 4.1 as in Remark 6.3). In the coset
monogamy game — `A ≤ 𝔽₂^n` the span of the first `n/2` columns of a uniform change of basis `U`,
`s ←$ CS(A)`, `t ←$ CS(A^⊥)`, `𝒜_M` receives `|A_{s,t}⟩` and splits it into `𝐋𝐑`; `𝒜_L` gets
`(U, r_L)` and returns `b^l_0`, `𝒜_R` gets `(U, r_R)` and returns `b^r_1`, `r_L, r_R ←$ 𝔽₂^n`; the
adversary wins iff `b^l_0 ⊕ b^r_1 = ⟨r_L, s⟩ ⊕ ⟨r_R, t⟩` — for any adversary `𝒜`,
`Pr[CosetMonogamy(𝒜, 1^λ) = 1] ≤ 1/2 + negl(λ)`.

**Formalization Note** `n = n(λ)` is even, polynomially bounded and `≥ λ` (the setting of §6,
Definition 6.1, p.32). Adversaries are unbounded: any finite registers `𝐋, 𝐑`, any isometry
`𝐌 → 𝐋𝐑` (`cosetWinProb` explains why isometries suffice), any two-outcome measurements depending
on `(U, r)`. The negligible function is chosen before the adversary. -/
theorem theorem_6_2 (n : ℕ → ℕ) (hn : PPADSIS.SubexpSIS.PolyBounded n)
    (hnl : ∀ l, l ≤ n l ∧ Even (n l)) :
    ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
      ∀ (l : ℕ) (L R : Type) [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
        (V : Matrix (L × R) (Bits (Fin (n l))) ℂ), IsIsometry V →
        ∀ (PL : GL (Fin (n l)) (ZMod 2) → Bits (Fin (n l)) → Matrix L L ℂ)
          (PR : GL (Fin (n l)) (ZMod 2) → Bits (Fin (n l)) → Matrix R R ℂ),
          (∀ U r, IsEffect (PL U r)) → (∀ U r, IsEffect (PR U r)) →
          cosetWinProb (n l) V PL PR ≤ 1 / 2 + ν l := by sorry

end QubitTracking
