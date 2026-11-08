-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_18
-- name    : RandGraphStates.lemma_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:29.168499+00:00
-- url     : https://prove2.me/theorems/7fa19e2c-df18-411f-bd7f-d73c398e185a
-- title:
--   Lemma 4.18: sharp affine nullity tail
-- statement:
--   Fix $\gamma>0$, $0<\varepsilon<\eta<1/2$, and $c_*>0$ with $c_*^2/2<\gamma c_{\eta,\varepsilon}$. Suppose $\gamma n\le m\le n$, $p_-\ge\log n/\sqrt n$ and $1\ll t\le c_*\sqrt n$. Then, for any deterministic symmetric matrices $\Gamma$ with zero diagonal,
--   $$
--   \Pr\bigl(\mathrm{Nullity}(A_m(p)+\Gamma)\ge t\bigr)\le(1+o(1))\,\pi^{1/2}_m(t).
--   $$
--   The factor $1+o(1)$ is what the second-moment argument of Theorem 4.20 requires.
--
--   Differences from the source:
--   - encoding: o(1), uniformly in the listed parameters → ∀ δ > 0, ∃ thresholds depending only on the fixed constants, ∀ parameters: the bound with δ; reason: the two forms are equivalent by a diagonal argument; uniformity is written by the quantifier order
--   - reading: unsubscripted log in the hypothesis on p₋ → natural logarithm Real.log; reason: the proofs use |q| ≤ e^(−2p₋) and log(e/p₋); natural log gives the weaker hypothesis, so the stronger theorem, which implies the base-2 reading
--   - encoding: c_{η,ε} > 0 as in Proposition 4.12 → no separate hypothesis; reason: it follows from c_*²/2 < γ c_{η,ε} with γ > 0; it adds nothing
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.18, p.32

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Lemma 4.18** (sharp affine nullity tail). Fix `γ > 0`, `0 < ε < η < 1/2`, and `c_* > 0` with
`c_*²/2 < γ c_{η,ε}`. If `γn ≤ m ≤ n`, `p₋ ≥ log n/√n`, `1 ≪ t ≤ c_* √n`, then for any deterministic symmetric
`Γ` with zero diagonal, `Pr(Nullity(A_m(p) + Γ) ≥ t) ≤ (1 + o(1)) π^{1/2}_m(t)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.18, p.32.

**Formalization Note.** The asymptotics are unfolded: for each `δ > 0` there are `N, T`, depending only on the fixed
constants, uniform over `m, p, t, Γ`. The bound is `π^{1/2}_m(t)`, with its supremum over diagonals, as printed. `log` is
natural. -/
theorem lemma_4_18 (γ ε η cstar : ℝ) (hγ : 0 < γ) (hε : 0 < ε) (hεη : ε < η) (hη : η < 1 / 2)
    (hc : 0 < cstar) (hcc : cstar ^ 2 / 2 < γ * cEtaEps η ε) :
    ∀ δ : ℝ, 0 < δ → ∃ N T : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ, γ * n ≤ m → m ≤ n →
      ∀ p : ℝ, 0 < p → p < 1 → Real.log n / Real.sqrt n ≤ pMinus p →
      ∀ t : ℕ, T ≤ t → (t : ℝ) ≤ cstar * Real.sqrt n → ∀ Γ : ZeroDiagSymm m,
      gnpProb m p (fun G => t ≤ nullity (adjF2 G + Γ.1)) ≤ (1 + δ) * piTail (1 / 2) m t := by sorry

end RandGraphStates
