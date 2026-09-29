-- Prove2me | Theorems.Thm_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
-- name    : RegularSingular.hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/36f0e1f2-e351-57e8-95f0-bcdfae97f155
-- title:
--   Term-by-term differentiation of y^e(log y)ⁿ expansions
-- statement:
--   Let $\iota$ be a finite index type, $r$ a natural number, and let the functions take values in $\mathbb{C}^{r}$ (Lean: `Fin r → ℂ`). Given exponents $e : \iota \to \mathbb{C}$ and $n : \iota \to \mathbb{N}$ such that $i \mapsto (e_i, n_i)$ is injective, and a real $\theta$ with $\operatorname{Re} e_i < \theta$ for every $i$, consider $F, F_z : \mathbb{R} \times \mathbb{R} \to \mathbb{C}^{r}$ (written as functions of $y$ then $z$) and families $c, g : \iota \to \mathbb{R} \to \mathbb{C}^{r}$ subject to: for each $y \in (0,1]$ and each $z \in (0,2]$, the map $z \mapsto F(y,z)$ has derivative $F_z(y,z)$ at $z$; for each $y \in (0,1]$, $z \mapsto F_z(y,z)$ is continuous on $(0,2]$; each $g_i$ is continuous on $(0,2]$; for each $z \in (0,2]$ there is a constant $K$ (allowed to depend on $z$) with $\bigl\|F(y,z) - \sum_i (y^{e_i} (\log y)^{n_i})\, c_i(z)\bigr\| \le K y^{\theta}$ for all $y \in (0,1]$; and for each $z_0 \in (0,2]$ there are $K$ and $\varepsilon > 0$ with $\bigl\|F_z(y,z) - \sum_i (y^{e_i} (\log y)^{n_i})\, g_i(z)\bigr\| \le K y^{\theta}$ for all $z \in (0,2]$ with $|z - z_0| < \varepsilon$ and all $y \in (0,1]$. The conclusion is that for every $i$ and every $z$ in the open interval $(0,2)$, the coefficient function $c_i$ has derivative $g_i(z)$ at $z$.
--
--   This is the standard term-by-term differentiation principle for asymptotic expansions along pairwise distinct terms $y^{e_i}(\log y)^{n_i}$, with respect to a parameter $z$, the expansion of the $z$-derivative being assumed locally uniform in $z$; uniqueness of the coefficients is supplied by [`LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow`](thm.html#LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow). It is used in the analysis of regular singular systems, in particular in the construction of two-level expansions for commuting systems and in the threshold statements for the ratio coefficients of flat regular singular systems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RegularSingular.hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
    {ι : Type*} [Fintype ι] (r : ℕ) (e : ι → ℂ) (n : ι → ℕ)
    (hinj : Function.Injective fun i => (e i, n i)) (θ : ℝ) (hθ : ∀ i, (e i).re < θ)
    (F Fz : ℝ → ℝ → (Fin r → ℂ)) (c g : ι → ℝ → (Fin r → ℂ))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt (fun z => F y z) (Fz y z) z)
    (hFz : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn (fun z => Fz y z) (Set.Ioc 0 2))
    (hg : ∀ i, ContinuousOn (g i) (Set.Ioc 0 2))
    (hexpF : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∃ K : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z - ∑ i, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ n i) • c i z‖ ≤ K * y ^ θ)
    (hexpFz : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖Fz y z - ∑ i, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ n i) • g i z‖ ≤ K * y ^ θ) :
    ∀ i, ∀ z ∈ Set.Ioo (0 : ℝ) 2, HasDerivAt (c i) (g i z) z := by sorry
