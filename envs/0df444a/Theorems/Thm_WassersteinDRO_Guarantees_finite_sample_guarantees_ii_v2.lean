-- Prove2me | Theorems.Thm_WassersteinDRO_Guarantees_finite_sample_guarantees_ii_v2
-- name    : WassersteinDRO.Guarantees.finite_sample_guarantees_ii_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:38.557064+00:00
-- url     : https://prove2.me/theorems/f193f525-6c02-46dc-873e-9a1d834e48ee
-- title:
--   Theorem 22(a) — finite sample guarantee II: $\mathbb{P}^N\{R(P,\ell) \le R_\varepsilon(\hat\mu,\hat\Sigma,\ell)\ \forall\ell\} \ge 1-\eta$ with the Theorem-21 constant $c$
-- statement:
--   Fix a dimension $m$, a mean vector $\mu \in \mathbb{R}^m$, a covariance matrix $\Sigma \in \mathbb{S}^m_+$, and light-tail parameters $\alpha > 2$, $A > 0$. There is a constant $c > 1$, depending only on $(\mu,\Sigma,\alpha,A,m)$ — the constant of the concentration inequality of Theorem 21, eq. (28) — such that the following holds for every probability distribution $P$ on $\mathbb{R}^m$ with mean vector $\mu$, covariance matrix $\Sigma$ and $\mathbb{E}_P[\exp(\|\xi\|_2^\alpha)] \le A$, every sample size $N \ge 1$, every closed set $\Xi \subseteq \mathbb{R}^m$ containing the support of $P$, and every class $\mathcal{L}$ of measurable upper semicontinuous loss functions $\ell : \mathbb{R}^m \to \mathbb{R}$: for all $\eta \in (0,1)$ and all $\varepsilon \ge \varepsilon_N(\eta) = \log(c/\eta)/\sqrt{N}$,
--   $$\mathbb{P}^N\Big\{R(P,\ell) \le R_\varepsilon(\hat\mu,\hat\Sigma,\ell)\ \ \forall \ell \in \mathcal{L}\Big\} \;\ge\; 1-\eta,$$
--   where $\mathbb{P}^N$ is the law of the $N$ i.i.d. training samples $\hat\xi_1,\dots,\hat\xi_N \sim P$, $\hat\mu$ and $\hat\Sigma$ are the mean vector and covariance matrix of the empirical distribution $\hat P_N = \frac1N\sum_i \delta_{\hat\xi_i}$, $R(P,\ell) = \mathbb{E}_P[\ell]$ is the true risk, and $R_\varepsilon(\hat\mu,\hat\Sigma,\ell) = \sup_{Q \in \mathcal{G}_\varepsilon(\hat\mu,\hat\Sigma)} \mathbb{E}_Q[\ell]$ is the Gelbrich risk (18) over the Gelbrich hull (Definition 2) of distributions supported on $\Xi$ with finite second moments whose mean and covariance lie in the Gelbrich uncertainty set $\mathcal{U}_\varepsilon(\hat\mu,\hat\Sigma)$; risks are extended-real with the paper's p. 2 convention. In words: with probability at least $1-\eta$ over the training sample, the Gelbrich risk is an upper confidence bound on the true risk uniformly over all admissible losses. (Part (b) of Theorem 22, eq. (29b), on an optimizer of the Gelbrich risk optimization problem (19), is not part of this statement.)
--
--   **Formalization Note.** The retired version was false because the constant $c$ of $\varepsilon_N(\eta) = \log(c/\eta)/\sqrt N$ was a free universally quantified real $> 1$ rather than the constant delivered by Theorem 21, so the radius could be fixed independently of the scale of $P$ (with $c = 2$, $N = 1$, $P = \tfrac12\delta_{10} + \tfrac12\delta_{-10}$ the Gelbrich ball misses the truth with probability $\tfrac12$). The new statement does the following differently. (i) $c$ is existentially quantified after $(m,\mu,\Sigma,\alpha,A)$ and before $P$, $N$, $\Xi$, $\mathcal{L}$, $\eta$, $\varepsilon$, exactly as in Theorem 21 ("depends on $P$ only through $\mu,\Sigma,\alpha,A$ and $m$") and as in the milestone `concentration_inequalities_ii`; the guarantee holds with the same constant. (ii) The Gelbrich hull now requires finite second moments (`gelbrichHull` v2), as Definition 2 presupposes, instead of admitting measures without a covariance matrix through a junk-valued integral; the Gelbrich risk and the true risk are the paper's extended-real expectations with its p. 2 convention (`gelbrichRisk`/`nominalRisk` v2) instead of a supremum discarding non-integrable $Q$, so the retired extra hypothesis "every $\ell \in \mathcal{L}$ is $P$-integrable", which the source does not state, is dropped. (iii) Standing assumptions made explicit: $\Xi$ is closed and contains the support of $P$ (p. 6); every $\ell \in \mathcal{L}$ is measurable (p. 1) and upper semicontinuous (Assumption 1, p. 9, tacitly in force throughout); $\hat P_N$-integrability of Assumption 1 is automatic for the empirical distribution and not repeated; $N \ge 1$; $\hat\mu,\hat\Sigma$ are the moments of the empirical distribution (the paper's definition of the sample mean and sample covariance, Section 4.3); $\|\cdot\|_2$ is the Euclidean norm of `EuclideanSpace ℝ (Fin m)`, as in (28); the light-tail condition $\mathbb{E}_P[\exp(\|\xi\|_2^\alpha)] \le A$ is written as integrability plus the bound on the integral; the event's probability is the (outer) measure of the set under $P^N = P^{\otimes N}$. Losses are taken real-valued, a special case of the paper's extended-real-valued losses that the retired version already made. No correction to the printed source.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), Theorem 22, p. 23–24, eq. (29a) (conditions of Theorem 21 and eq. (28), p. 23; Definition 2, p. 17; eq. (18), p. 18)

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_empiricalDistribution
import Definitions.Def_WassersteinDRO_Guarantees_nominalRisk_v2
import Definitions.Def_WassersteinDRO_Guarantees_gelbrichRisk_v2
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- Theorem 22 (Finite sample guarantees II), part (a), Kuhn, Mohajerin Esfahani, Nguyen &
Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization*, INFORMS TutORials
2019 (arXiv:1908.08729v2), p. 23–24, eq. (29a): assume all conditions of Theorem 21 hold and
`ε_N(η) = log(c/η)/√N` as in (28). Then for all `η ∈ (0,1)` and `ε ≥ ε_N(η)`,
`P^N { R(P,ℓ) ≤ Rε(µ̂,Σ̂,ℓ) ∀ℓ ∈ L } ≥ 1 - η`. (Part (b), eq. (29b), concerns an optimizer
of the Gelbrich risk optimization problem (19) and is not part of this statement.)

The conditions of Theorem 21 (p. 23): the unknown true distribution `P` on `ℝ^m` has mean
vector `µ` and covariance matrix `Σ`, and is light-tailed, `E_P[exp(‖ξ‖₂^α)] ≤ A` for some
`α > 2`, `A > 0`; the constant `c > 1` of (28) "depends on `P` only through `µ, Σ, α, A` and
`m`". Accordingly `c` is existentially quantified *after* `(m, µ, Σ, α, A)` and *before* `P`,
the sample size, the support set and the loss class: one constant serves every `P` sharing
these parameters, and the guarantee holds with the same `c` as the concentration inequality
of Theorem 21 (`concentration_inequalities_ii`). Standing framework (p. 1, 6, 9): `Ξ` is a
closed set containing the support of `P` (`P Ξᶜ = 0`); every `ℓ ∈ L` is measurable and
(Assumption 1, tacitly in force throughout) upper semicontinuous; `P̂_N`-integrability is
automatic for the empirical distribution. `µ̂ = E_{P̂_N}[ξ]` and `Σ̂ = Cov_{P̂_N}[ξ]` are the mean
and covariance of the empirical distribution `P̂_N` of the `N ≥ 1` i.i.d. training samples,
`P^N` is the law of the sample, and the norm on `ℝ^m = EuclideanSpace ℝ (Fin m)` is the
Euclidean norm `‖·‖₂` of (28). `R(P,ℓ)` and the Gelbrich risk are taken in `EReal` with the
paper's convention for non-integrable losses (`nominalRisk`/`gelbrichRisk` v2), so no
integrability of `ℓ` under `P` has to be assumed.

Corrected from the retired `finite_sample_guarantees_ii`: `c` was a free universally
quantified real `> 1` instead of the constant delivered by Theorem 21 (so the radius could be
chosen independently of the scale of `P` and the guarantee failed); `IsClosed Ξ`,
measurability and upper semicontinuity of the losses were missing; an extra hypothesis
`∀ ℓ ∈ L, Integrable ℓ P` not in the source was imposed; and the Gelbrich hull/risk admitted
distributions without second moments through a junk value and dropped non-integrable `Q`
(now `gelbrichHull`/`gelbrichRisk` v2). -/
theorem finite_sample_guarantees_ii_v2 {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) (α A : ℝ)
    (hα : 2 < α) (hA : 0 < A) :
    ∃ c : ℝ, c > 1 ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ),
        IsProbabilityMeasure P → 0 < N →
        meanVector P = μ → covarianceMatrix P = Sigma →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
        ∀ (Ξ : Set (EuclideanSpace ℝ (Fin m))), IsClosed Ξ → P Ξᶜ = 0 →
        ∀ (L : Set (EuclideanSpace ℝ (Fin m) → ℝ)),
          (∀ ℓ ∈ L, Measurable ℓ ∧ UpperSemicontinuous ℓ) →
        ∀ η ε : ℝ, 0 < η → η < 1 → ε ≥ Real.log (c / η) / Real.sqrt N →
          sampleMeasure P N
              {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
                ∀ ℓ ∈ L, nominalRisk P ℓ ≤
                  gelbrichRisk ε Ξ (meanVector (empiricalDistribution ξhat))
                    (covarianceMatrix (empiricalDistribution ξhat)) ℓ} ≥
            ENNReal.ofReal (1 - η) := by sorry

end WassersteinDRO.Guarantees
