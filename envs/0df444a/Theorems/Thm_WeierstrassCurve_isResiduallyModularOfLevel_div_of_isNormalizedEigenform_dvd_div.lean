-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/ed237c7c-e4ee-5405-bcfb-ce8171547062
-- title:
--   Residual modularity at level M/p from an eigenform of divisor level
-- statement:
--   Fix a prime $p$ and natural numbers $L$, $M$, $N''$ with $M \neq 0$, and a Weierstrass curve $W$ over $\mathbb{Z}$. Assume $L \mid M$, $p^{2} \mid L$, and $N'' \mid M/p$. Let $S_{0}$ be a set of natural numbers such that every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M/p$ and $\ell \neq p$ satisfies $\ell \notin S_{0}$. Let $f$ be a weight-$2$ cusp form on $\Gamma_{0}(N'')$ which is a normalised eigenform in the sense of the project's structure: its $q$-expansion coefficients (of width $1$) satisfy $a_{1}(f) = 1$, multiplicativity $a_{mn}(f) = a_{m}(f)a_{n}(f)$ for coprime $m,n$, the recursion $a_{q^{r+2}}(f) = a_{q}(f)a_{q^{r+1}}(f) - q\,a_{q^{r}}(f)$ for primes $q \nmid N''$, and $a_{q^{r+2}}(f) = a_{q}(f)a_{q^{r+1}}(f)$ for primes $q \mid N''$. Let $\mathfrak{m}'$ be a maximal ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, and suppose that for every prime $\ell$ with $\ell \nmid N''$ and $\ell \notin S_{0}$ there is an algebraic integer $a$ with $a = a_{\ell}(f)$ in $\mathbb{C}$ and $a - a_{\ell}(W) \in \mathfrak{m}'$, where $a_{\ell}(W) = \ell + 1 - \#(W \bmod \ell)$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$. The conclusion is that $W$ is residually modular of level $M/p$ at $p$: there are a weight-$2$ cusp form $g$ on $\Gamma_{0}(M/p)$ that is a normalised eigenform in the above sense and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M/p$ and $\ell \neq p$ there is an algebraic integer $a$ with $a = a_{\ell}(g)$ in $\mathbb{C}$ and $a - a_{\ell}(W) \in \mathfrak{m}$.
--
--   This is the final bookkeeping step of the level-lowering chain, converting a curve-congruent eigenform of some level dividing $M/p$ into the statement of residual modularity at level $M/p$ itself, the shape in which the congruence data is consumed further on. It is used in the deduction [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div.lean

import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNormalizedEigenform_dvd_div {p L M N'' : ℕ} [Fact p.Prime] [NeZero M]
    {W : WeierstrassCurve ℤ}
    (hLM : L ∣ M) (hpL : p ^ 2 ∣ L) (hN'' : N'' ∣ M / p)
    (S₀ : Set ℕ)
    (hS₀rev : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M / p → ℓ ≠ p → ℓ ∉ S₀)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N'') 2} {𝔪' : Ideal (integralClosure ℤ ℂ)}
    (hf : f.IsNormalizedEigenform) (h𝔪' : 𝔪'.IsMaximal)
    (hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪')
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N'' → ℓ ∉ S₀ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪') :
    W.IsResiduallyModularOfLevel p (M / p) := by sorry
