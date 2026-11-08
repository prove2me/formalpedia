-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_19
-- name    : RandGraphStates.lemma_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:36.70723+00:00
-- url     : https://prove2.me/theorems/bac7981f-a7c7-4b83-b0b3-669090f67a4a
-- title:
--   Lemma 4.19: $p$-biased conditional extension
-- statement:
--   Fix constants $\gamma,\kappa>0$ and $c>0$ such that $c^2/2<\gamma c_{\eta,\varepsilon}$, where $0<\varepsilon<\eta<1/2$, and assume $p_-\ge(\log n)/\sqrt n$ and $1\ll t\le c\sqrt n$. Let $M_0$ be a fixed symmetric zero-diagonal matrix of size $h$ with $d:=\mathrm{Nullity}(M_0)\le\kappa\sqrt n$. Let $s\ge\gamma n$, $h+s\le n$, and
--   $$
--   M=\begin{bmatrix}M_0&Y\\Y^{T}&A_s(p)\end{bmatrix},
--   $$
--   where $Y$ has independent $\mathrm{Ber}(p)$ entries and is independent of $A_s(p)$. If $t\equiv h+s\pmod 2$, then, for all such $M_0,h,s$,
--   $$
--   \Pr\bigl(\mathrm{Nullity}(M)\ge t\mid M_0\bigr)\le(1+o(1))\,\pi^{1/2}_{h+s}(t).
--   $$
--   This controls the correlation of two overlapping principal submatrices in the second moment.
--
--   Differences from the source:
--   - encoding: o(1), uniformly in the listed parameters → ∀ δ > 0, ∃ thresholds depending only on the fixed constants, ∀ parameters: the bound with δ; reason: the two forms are equivalent by a diagonal argument; uniformity is written by the quantifier order
--   - reading: unsubscripted log in the hypothesis on p₋ → natural logarithm Real.log; reason: the proofs use |q| ≤ e^(−2p₋) and log(e/p₋); natural log gives the weaker hypothesis, so the stronger theorem, which implies the base-2 reading
--   - reading: c_{η,ε} with η, ε not bound in the paragraph → any fixed 0 < ε < η < 1/2; reason: the domain of c_{η,ε} on p.26, and the use in Theorem 4.20 chooses them
--   - encoding: A_s(p), Pr(· | M_0) → blockTail at the zero diagonal, with M_0 a fixed parameter; reason: A_s(p) has zero diagonal; conditioning on a fixed block, as the paper writes it
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §4.4, standing paragraph, and Lemma 4.19, p.34

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

/-- **Lemma 4.19** (`p`-biased conditional extension). Fix `0 < ε < η < 1/2` and `γ, κ, c > 0` with
`c²/2 < γ c_{η,ε}`, and assume `p₋ ≥ (log n)/√n`, `1 ≪ t ≤ c√n`. Let `M₀` be a fixed symmetric zero-diagonal matrix of
size `h`, with `Nullity(M₀) ≤ κ√n`, let `s ≥ γn`, `h + s ≤ n`, and `M = [M₀ Y; Yᵀ A_s(p)]` with `Y` having independent
`Ber(p)` entries, independent of `A_s(p)`. If `t ≡ h + s (mod 2)`, then for all such `M₀, h, s`,
`Pr(Nullity(M) ≥ t | M₀) ≤ (1 + o(1)) π^{1/2}_{h+s}(t)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), §4.4, standing paragraph and Lemma 4.19, p.34.

**Formalization Note.** The standing paragraph above the lemma is part of the statement. The asymptotics are unfolded:
for each `δ > 0` there are `N, T`, depending only on the fixed constants, uniform over `p, t, h, s, M₀`. `A_s(p)` has zero
diagonal, so `blockTail` is taken at the zero diagonal vector. `log` is natural. -/
theorem lemma_4_19 (γ κ c ε η : ℝ) (hγ : 0 < γ) (hκ : 0 < κ) (hc : 0 < c)
    (hε : 0 < ε) (hεη : ε < η) (hη : η < 1 / 2) (hcc : c ^ 2 / 2 < γ * cEtaEps η ε) :
    ∀ δ : ℝ, 0 < δ → ∃ N T : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ p : ℝ, 0 < p → p < 1 → Real.log n / Real.sqrt n ≤ pMinus p →
      ∀ t : ℕ, T ≤ t → (t : ℝ) ≤ c * Real.sqrt n →
      ∀ h s : ℕ, γ * n ≤ s → h + s ≤ n → t ≡ h + s [MOD 2] →
      ∀ M0 : ZeroDiagSymm h, (nullity M0.1 : ℝ) ≤ κ * Real.sqrt n →
      blockTail p M0.1 (0 : Fin s → ZMod 2) t ≤ (1 + δ) * piTail (1 / 2) (h + s) t := by sorry

end RandGraphStates
