-- Prove2me | Theorems.Thm_PhaseEncodedQGE_corollary_A_6
-- name    : PhaseEncodedQGE.corollary_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:44.896668+00:00
-- url     : https://prove2.me/theorems/22e34f4c-f9a2-4b6e-94a8-3b9b38436eca
-- title:
--   Corollary A.6 — extremal-count form of the X-mixer value
-- statement:
--   Let $r\ge1$, $h=h^{X,r}$. The profile is even under $k\mapsto3-k$: $h(0)=h(3)=:h_e$ and $h(1)=h(2)=:h_o$, where
--   $$h_e=\sum_{b\le r}\cos3b\gamma,\qquad h_o=\sum_{b\le r}\cos b\gamma .$$
--   Hence, for a cubic graph $G$ on $n$ vertices with the degree-aware preparation, $t=\tan(\eta/2)$, and every outcome with $|D|=m$,
--   $$\frac{p_1(x)}{p_0(x)}=\frac{(h_e-h_o)E_{\mathrm{out}}(D)+(n-m)h_o}{t}-t\bigl[(h_e-h_o)E_{\mathrm{in}}(D)+m\,h_o\bigr].$$
--
--   The X-mixer value thus depends on $D$ only through the two extremal counts, given $n$ and $m$.
--
--   Differences from the source:
--   - generalization: the X-mixer members PE-X1, PE-X2 ($r\in\{1,2\}$) → every number $r\ge1$ of tied repetitions, $h=h^{X,r}$; reason: Theorem 3.2 and Corollary A.6 are stated for r tied repetitions and the proof uses only the evenness of h^{X,r}; r = 1, 2 are special cases
--   - encoding: $\lambda=p_1/p_0$ and $t^{\pm1}$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t, 1/t or p₁/p₀ is undefined (Lean's x/0 = 0 would otherwise give junk values)
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.2, p.15 (PDF p.16), Corollary A.6, eq. (27)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Corollary A.6, the extremal-count form (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.2, p.15, eq. (27)).

For the X-mixer members the profile `h^{X,r}` is even under `k ↦ 3 − k`: `h(0) = h(3) =: h_e` and
`h(1) = h(2) =: h_o`, where `h_e = ∑_{b≤r} cos 3bγ` and `h_o = ∑_{b≤r} cos bγ`. Hence for every
outcome with `|D| = m` (cubic `G`, degree-aware preparation, `t = tan(η/2)`),
`p₁(x)/p₀(x) = [(h_e − h_o)E_out(D) + (n − m)h_o]/t − t[(h_e − h_o)E_in(D) + m h_o]`.

**Formalization Note** "X-mixer members" are taken at every `r ≥ 1` (the paper's members are
`r = 1, 2`). `cos(η/2) ≠ 0 ≠ sin(η/2)` exclude undefined `t^{±1}` and `p₁/p₀`. -/
theorem corollary_A_6 (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) :
    (∀ k : ℕ, k ≤ 3 → hX r γ (3 - k) = hX r γ k) ∧
    hX r γ 0 = hX r γ 3 ∧ hX r γ 1 = hX r γ 2 ∧
    hX r γ 0 = ∑ b ∈ Finset.Icc 1 r, Real.cos (3 * (b : ℝ) * γ) ∧
    hX r γ 1 = ∑ b ∈ Finset.Icc 1 r, Real.cos ((b : ℝ) * γ) ∧
    (∀ (n m : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ x : Outcome n, (defects x).card = m →
        firstOrder (degPrep G η) .X r G γ x =
          ((hX r γ 0 - hX r γ 1) * (Eout G (defects x) : ℝ) + ((n : ℝ) - m) * hX r γ 1) /
              Real.tan (η / 2) -
            Real.tan (η / 2) * ((hX r γ 0 - hX r γ 1) * (Ein G (defects x) : ℝ) + m * hX r γ 1))
    := by sorry

end PhaseEncodedQGE
