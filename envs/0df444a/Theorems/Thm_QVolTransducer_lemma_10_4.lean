-- Prove2me | Theorems.Thm_QVolTransducer_lemma_10_4
-- name    : QVolTransducer.lemma_10_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:17.88819+00:00
-- url     : https://prove2.me/theorems/5d4a608f-ed23-4e2e-8f1b-f9aec3b52d3e
-- title:
--   Lemma 10.4 — mean and relative variance of $X_{\beta',\beta}$ through the partition function
-- statement:
--   Let $d\ge1$, $R\ge1$, and let $K$ be a convex body with $B_d\subseteq K\subseteq RB_d$. Let $H(x)=\|x\|^2$, let $\beta'<\beta$ be reals, and let $X_{\beta',\beta}(x):=\exp(-(\beta'-\beta)H(x))$. Then there is $\xi\in[\beta',\beta]$ such that
--
--   $$
--   \mathbb E_{x\sim\pi_\beta}[X_{\beta',\beta}(x)]=\frac{Z(\beta')}{Z(\beta)}=\exp\bigl(\mathbb E_{x\sim\pi_\xi}[H(x)]\,(\beta-\beta')\bigr),
--   $$
--
--   and there is $\xi\in[2\beta'-\beta,\beta]$ such that
--
--   $$
--   \frac{\mathrm{Var}_{x\sim\pi_\beta}[X_{\beta',\beta}(x)]}{\mathbb E_{x\sim\pi_\beta}[X_{\beta',\beta}(x)]^2}=\frac{Z(2\beta'-\beta)Z(\beta)}{Z(\beta')^2}-1=\exp\bigl(\mathrm{Var}_{x\sim\pi_\xi}[H(x)]\,(\beta'-\beta)^2\bigr)-1 .
--   $$
--
--   Here $Z$ and $\pi_\beta$ are the partition function and Gibbs distribution of $K$. These identities express the mean and relative variance of each cooling-stage estimator through the moments of $\|x\|^2$.
--
--   Differences from the source:
--   - reading: B_d ⊆ K ⊆ RB_d → K compact and convex with B_d ⊆ K ⊆ RB_d; reason: Z and π_β are defined for convex bodies (Definition 5.1, p.36), the standing object of Part II (trap 19)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Lemma 10.4, p.70 (PDF p.72)

import Mathlib
import Definitions.Def_QVolTransducer_partitionFn

namespace QVolTransducer

/-- **Mean and relative variance of the cooling estimators** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Lemma 10.4, p.70 (PDF p.72)).

Let `d ≥ 1`, `R ≥ 1`, `K` a convex body with `B_d ⊆ K ⊆ RB_d`, `H(x) = ‖x‖²`, `β' < β`, and
`X_{β',β}(x) = exp(−(β' − β)H(x))`. Then there is `ξ ∈ [β', β]` with
`E_{x∼π_β}[X_{β',β}(x)] = Z(β')/Z(β) = exp(E_{x∼π_ξ}[H(x)] (β − β'))`, and there is
`ξ ∈ [2β' − β, β]` with
`Var_{π_β}[X_{β',β}] / E_{π_β}[X_{β',β}]² = Z(2β' − β)Z(β)/Z(β')² − 1 = exp(Var_{x∼π_ξ}[H(x)] (β' − β)²) − 1`.

**Formalization Note** The Gibbs distributions `π_β` and the partition function `Z` are those of
Definition 5.1 (p.36), defined for a convex body `K`; this standing assumption of Part II is
stated as `IsCompact K` and `Convex ℝ K`. `β`, `β'` and `ξ` are arbitrary reals (possibly
negative). -/
theorem lemma_10_4 (d : ℕ) (R : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) (β' β : ℝ)
    (hd : 1 ≤ d) (hR : 1 ≤ R) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hBK : Metric.closedBall 0 1 ⊆ K) (hKR : K ⊆ Metric.closedBall 0 R) (hββ : β' < β) :
    (∃ ξ ∈ Set.Icc β' β,
      gibbsMean K β (fun x => Real.exp (-(β' - β) * ‖x‖ ^ 2)) =
          partitionFn K β' / partitionFn K β ∧
        partitionFn K β' / partitionFn K β =
          Real.exp (gibbsMean K ξ (fun x => ‖x‖ ^ 2) * (β - β'))) ∧
    (∃ ξ ∈ Set.Icc (2 * β' - β) β,
      gibbsVar K β (fun x => Real.exp (-(β' - β) * ‖x‖ ^ 2)) /
          gibbsMean K β (fun x => Real.exp (-(β' - β) * ‖x‖ ^ 2)) ^ 2 =
          partitionFn K (2 * β' - β) * partitionFn K β / partitionFn K β' ^ 2 - 1 ∧
        partitionFn K (2 * β' - β) * partitionFn K β / partitionFn K β' ^ 2 - 1 =
          Real.exp (gibbsVar K ξ (fun x => ‖x‖ ^ 2) * (β' - β) ^ 2) - 1) := by sorry

end QVolTransducer
