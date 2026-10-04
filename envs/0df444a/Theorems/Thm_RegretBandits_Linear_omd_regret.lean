-- Prove2me | Theorems.Thm_RegretBandits_Linear_omd_regret
-- name    : RegretBandits.Linear.omd_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:32:43.34344+00:00
-- url     : https://prove2.me/theorems/b323aa43-e385-4b9b-b897-5c04c4db3de0
-- title:
--   Theorem 5.3 — regret of Online Mirror Descent with a Legendre function
-- statement:
--   Let $K$ be a compact convex set, $D$ an open convex set with $K\subseteq\bar D$ and $K\cap D\ne\emptyset$, $F$ a Legendre function on $\bar D$, and $\eta>0$. Let $\ell_1,\ell_2,\dots$ be losses on $K$. Let $x_1,x_2,\dots$ be an OMD run in which round $t$ uses a subgradient $g_t=\nabla\ell_t(x_t)$ of $\ell_t$ at $x_t$, that is,
--   $$\ell_t(x_t)-\ell_t(y)\le g_t^\top(x_t-y)\qquad\text{for all }y\in K,$$
--   and in which every dual step is well defined (the consistency condition (5.3)). Then for every $n$ and every $x\in K$,
--   $$\sum_{t=1}^n\ell_t(x_t)-\sum_{t=1}^n\ell_t(x)\ \le\ \frac{F(x)-F(x_1)}{\eta}+\frac1\eta\sum_{t=1}^nD_{F^*}\bigl(\nabla F(x_t)-\eta g_t,\ \nabla F(x_t)\bigr).$$
--
--   This is the basic full-information regret bound of mirror descent. Its right-hand side separates a "diameter" term, measured by $F$, from a "stability" term, measured in the dual by $D_{F^*}$. OSMD inherits it pathwise.
--
--   **Formalization Note** The book assumes that every loss in the class $\mathcal L$ is subdifferentiable and writes $\nabla\ell_t(x_t)$ for any subgradient (Definition 5.1). Here the subgradient used by the algorithm is an explicit input $g_t$, and only its defining inequality at $x_t$ is assumed. The consistency condition (5.3) is required along the run (each $w_{t+1}$ exists) rather than for all $(x,\ell)\in(K\cap D)\times\mathcal L$. Both choices weaken the hypotheses to exactly what the algorithm uses. Rounds are $t=1,\dots,n$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 72, Theorem 5.3 (with the OMD box and (5.3) on p. 71)

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_OMD

namespace RegretBandits.Linear

/-- Theorem 5.3 (Regret of OMD with a Legendre function; Bubeck, Cesa-Bianchi,
arXiv:1204.5721v2, p. 72). Let `K` be compact and convex, `F` Legendre on `D̄ ⊇ K` with
`K ∩ D ≠ ∅`, `η > 0`, and let `ℓ_1, ℓ_2, …` be losses on `K`. If `x_1, x_2, …` is an OMD run
whose step uses, in round `t`, a subgradient `g_t = ∇ℓ_t(x_t)` of `ℓ_t` at `x_t`
(`ℓ_t(x_t) - ℓ_t(y) ≤ g_tᵀ(x_t - y)` for all `y ∈ K`, Definition 5.1), then for every `x ∈ K`
`∑_{t=1}^n ℓ_t(x_t) - ∑_{t=1}^n ℓ_t(x) ≤ (F(x) - F(x_1))/η + (1/η) ∑_{t=1}^n D_{F*}(∇F(x_t) - η g_t, ∇F(x_t))`.
The consistency condition (5.3) is encoded in the run (`w_{t+1}` exists). -/
theorem omd_regret {d : ℕ} {F : (Fin d → ℝ) → ℝ} {D K : Set (Fin d → ℝ)}
    (hF : IsLegendre F D) (hKc : IsCompact K) (hKv : Convex ℝ K) (hKD : K ⊆ closure D)
    (hKne : (K ∩ D).Nonempty) {η : ℝ} (hη : 0 < η)
    (ℓ : ℕ → (Fin d → ℝ) → ℝ) (g x w : ℕ → Fin d → ℝ)
    (hsub : ∀ t, 1 ≤ t → ∀ y ∈ K, ℓ t (x t) - ℓ t y ≤ g t ⬝ᵥ (x t - y))
    (hrun : IsOMDRun F D K η g x w) (n : ℕ) :
    ∀ y ∈ K,
      ∑ t ∈ Finset.Icc 1 n, ℓ t (x t) - ∑ t ∈ Finset.Icc 1 n, ℓ t y ≤
        (F y - F (x 1)) / η +
          (1 / η) * ∑ t ∈ Finset.Icc 1 n,
            dualBregman F D (grad F (x t) - η • g t) (grad F (x t)) := by sorry

end RegretBandits.Linear
