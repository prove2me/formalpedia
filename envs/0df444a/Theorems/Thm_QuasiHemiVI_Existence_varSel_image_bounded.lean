-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_varSel_image_bounded
-- name    : QuasiHemiVI.Existence.varSel_image_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:37:58.160167+00:00
-- url     : https://prove2.me/theorems/b3fc6ffb-ea2f-40cd-b79b-1e51de811e37
-- title:
--   Proof of Theorem 3.8 (ii) — the set $S(C)$ is bounded
-- statement:
--   Let $V$ be a real reflexive Banach space and $X$, $Y$ real Banach spaces, and assume all hypotheses of Theorem 3.8: (HC), (HJ), (Hγ), (H0), (HT) with $h$ convex, (Hφ), (HK), (HC0) with the coercivity (3.2) holding uniformly in $v_0\in C_0$, $\gamma$ compact, and (3.19). Let $S(w)$, for $w\in C$, be the solution set in $K(w)$ of inequality (3.21). Then
--
--   $$
--   S(C)=\bigcup_{w\in C}S(w)\quad\text{is a bounded subset of } V.
--   $$
--
--   Boundedness of $S(C)$ is the alternative "$\Psi(C)$ bounded" in Kluge's fixed point theorem (Theorem 2.7), which is needed when $C$ is unbounded; it also yields the boundedness of $\Gamma(f)\subseteq S(C)$.
--
--   **Formalization Note** (HC0) is taken with (3.2) uniform in $v_0\in C_0$ (`HC0Unif`): the paper's proof uses a single function $r$ with $r(s)\to+\infty$ for test points $v_n\in C_0\cap K(w_n)$ that vary with $n$. With (3.2) only at each fixed $v_0\in C_0$, as printed, the claim is false (see the note of Theorem 3.8 (ii)).
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, pp. 1260–1261, proof of Theorem 3.8 (ii): "Furthermore, we claim that the set S(C) is bounded."

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued
import Definitions.Def_QuasiHemiVI_Existence_Hypotheses
import Definitions.Def_QuasiHemiVI_Existence_Problems

namespace QuasiHemiVI.Existence

/-- Proof of Theorem 3.8 (ii), pp. 1260–1261: under the hypotheses of Theorem 3.8, the set
`S(C) = ⋃_{w ∈ C} S(w)` is bounded. (HC0) is taken with (3.2) uniform in `v₀ ∈ C₀`
(`HC0Unif`): the proof uses one function `r` for test points `v_n ∈ C₀ ∩ K(w_n)` that vary with
`n`, and with (3.2) only at each fixed `v₀ ∈ C₀`, as printed, the claim is false. -/
theorem varSel_image_bounded {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hV : IsReflexive V)
    (C : Set V) (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) (C₀ : Set V)
    (hC : HC C) (hJ : LocallyLipschitz J) (hT : HT C T φ J γ π f h)
    (hhcvx : ConvexOn ℝ Set.univ h) (hφ : Hphi φ) (hK : HK C K) (hC0 : HC0Unif C K T φ J γ C₀)
    (hγ : IsCompactOperator γ) (h319 : Cond319 C φ) :
    Bornology.IsBounded (⋃ w ∈ C, varSel K T φ J γ π f w) := by sorry

end QuasiHemiVI.Existence
