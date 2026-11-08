-- Prove2me | Theorems.Thm_RandGraphStates_proposition_4_12
-- name    : RandGraphStates.proposition_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:19.027391+00:00
-- url     : https://prove2.me/theorems/ccb52b6a-716f-478a-819f-2feceeef9ea4
-- title:
--   Proposition 4.12: middle-weight kernel vectors
-- statement:
--   Let $\Gamma$ be a deterministic symmetric $m\times m$ matrix, $M:=A_m(p)+\Gamma$, with leading principal submatrices $M_j$. For $1\le L_0<L_1<j_0\le m$, define $\theta(w):=(1+|q|^w)/2$. Then
--   $$
--   \Pr\bigl(\mathcal E^{\mathrm{mid}}_{j_0,L_0,L_1}(M)\bigr)\le m\sum_{w=L_0+1}^{L_1}\binom mw\theta(w)^{j_0-w}.
--   $$
--   In particular, for fixed $\gamma>0$ and $0<\varepsilon<\eta<1/2$, if $\gamma n\le m\le n$, $p_-\ge(\log n)/\sqrt n$, and $j_0:=\lfloor\eta m\rfloor$, $L_0:=\lceil\log\log n/p_-\rceil$, $L_1:=\lfloor\varepsilon m\rfloor$, then, uniformly over $m$ and $\Gamma$,
--   $$
--   \Pr\bigl(\mathcal E^{\mathrm{mid}}_{j_0,L_0,L_1}(M)\bigr)\le2^{-(c_{\eta,\varepsilon}+o(1))m}.
--   $$
--   Here $\theta$ is local to this statement, and $\Gamma$ may have a nonzero diagonal. The estimate controls vectors of intermediate weight in the proof of Lemma 4.18.
--
--   Differences from the source:
--   - encoding: o(1), uniformly over m and Γ, with p = p(n) → ∀ δ > 0, ∃ N, ∀ n ≥ N, ∀ m, p, Γ admissible: the bound 2^{−(c − δ)m}; reason: equivalent by a diagonal argument (a uniform bound in p is the same as a bound for every sequence p(n)); o(1) of either sign reduces to the one-sided δ
--   - reading: unsubscripted log in the hypothesis on p₋ → natural logarithm Real.log; reason: the proofs use |q| ≤ e^(−2p₋) and log(e/p₋); natural log gives the weaker hypothesis, so the stronger theorem, which implies the base-2 reading
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Proposition 4.12, p.27

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

/-- **Proposition 4.12** (middle-weight kernel vectors). Let `Γ` be a deterministic symmetric `m × m` matrix,
`M := A_m(p) + Γ`, `θ(w) := (1 + |q|^w)/2`. For `1 ≤ L₀ < L₁ < j₀ ≤ m`,
`Pr(E^mid_{j₀,L₀,L₁}(M)) ≤ m Σ_{w=L₀+1}^{L₁} C(m,w) θ(w)^{j₀-w}`. In particular, if `γn ≤ m ≤ n`,
`p₋ ≥ (log n)/√n`, `j₀ := ⌊ηm⌋`, `L₀ := ⌈log log n / p₋⌉`, `L₁ := ⌊εm⌋`, then, uniformly over `m` and `Γ`,
`Pr(E^mid_{j₀,L₀,L₁}(M)) ≤ 2^{-(c_{η,ε}+o(1))m}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Proposition 4.12, p.27.

**Formalization Note.** `θ` is local to this statement. `γ > 0` and `0 < ε < η < 1/2` are fixed (p.26). The `o(1)`
is unfolded: for each `δ > 0` there is `N`, uniform over `m, p, Γ`, with the bound for `n ≥ N`. `log` is natural. -/
theorem proposition_4_12 :
    (∀ (p : ℝ), 0 < p → p < 1 → ∀ (m j0 L0 L1 : ℕ) (Γ : Matrix (Fin m) (Fin m) (ZMod 2)),
      Γ.IsSymm → 1 ≤ L0 → L0 < L1 → L1 < j0 → j0 ≤ m →
      gnpProb m p (fun G => Emid j0 L0 L1 (adjF2 G + Γ)) ≤
        (m : ℝ) * ∑ w ∈ Finset.Icc (L0 + 1) L1,
          (m.choose w : ℝ) * ((1 + |qOf p| ^ w) / 2) ^ (j0 - w)) ∧
    (∀ γ ε η : ℝ, 0 < γ → 0 < ε → ε < η → η < 1 / 2 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, γ * n ≤ m → m ≤ n → ∀ p : ℝ, 0 < p → p < 1 →
      Real.log n / Real.sqrt n ≤ pMinus p →
      ∀ Γ : Matrix (Fin m) (Fin m) (ZMod 2), Γ.IsSymm →
      gnpProb m p (fun G =>
          Emid ⌊η * m⌋₊ ⌈Real.log (Real.log n) / pMinus p⌉₊ ⌊ε * m⌋₊ (adjF2 G + Γ)) ≤
        (2 : ℝ) ^ (-(cEtaEps η ε - δ) * m)) := by sorry

end RandGraphStates
