-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_theorem_3
-- name    : SampQueryLB.WarmSLC.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:14:58.215675+00:00
-- url     : https://prove2.me/theorems/53c3bea1-b84d-463d-bd98-f9711f55814a
-- title:
--   Theorem 3 — Gaussian decoupling: $\|P_LP_F\|_{op}\le\rho<1/2$ along every path gives $\mathrm{TV}(P^{sh},P^{ind})\le\frac32\rho M$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $O$ a standard Borel seed space with a probability law, and consider a $q$-round adaptive linear measurement process ($q\ge1$) with batch sizes $m_1,\dots,m_q$ and local/far labels, as in Definition 3.1 and §3.3. For a seed value $\omega$ and a record $z\in\mathbb R^{m_1}\times\cdots\times\mathbb R^{m_q}$ let $L(\omega,z)$ and $F(\omega,z)$ be the spans of the local and of the far measurement vectors evaluated along $z$, and let $P^{sh}$, $P^{ind}$ be the laws of the full transcript $(\omega,Z_1,\dots,Z_q)$ when both groups measure the same $\Xi\sim N(0,I_E)$, respectively independent copies.
--
--   **Theorem 3.** Let $0\le\rho<1/2$ and suppose $\|P_{L(\omega,z)}P_{F(\omega,z)}\|_{op}\le\rho$ for every seed value $\omega$ and every $z$. Then, with $M=\sum_{k=1}^qm_k$,
--   $$\mathrm{TV}(P^{sh},P^{ind})\le\tfrac32\rho M,$$
--   and the same bound holds for the laws of the algorithm's transcript and of its output.
--
--   This comparison lets queries at separated locations be treated as if they saw independent Gaussian coefficients (Corollary 5.6).
--
--   **Formalization Note.** The conclusion is stated for the image of $P^{sh}$ and $P^{ind}$ under every measurable function of the full transcript; the identity gives the first bound and the transcript and output maps (Borel functions of the full transcript) give the others. $P_W$ is `W.starProjection`.
--
--   Differences from the source:
--   - encoding: Borel maps B_k(ω, Z_1, …, Z_{k−1}), L_k(ω, Z_1, …, Z_{k−1}) ∈ {local, far} → MeasProcess: measurable maps of (ω, whole record) that do not depend on rounds ≥ k; labels Bool (true = local); reason: non-anticipating maps of the whole record are exactly maps of the earlier rounds
--   - encoding: 'the same bound holds for the laws of the algorithm's transcript and of its output' → the bound for the image laws under every measurable function of the full transcript (f = id gives (4)/(42)); reason: the transcript and the output are Borel functions of the full transcript (§3.1); the quantified form contains both
--   - encoding: TV(·,·) = sup over measurable B of |ν(B) − ν'(B)| → TVAtMost μ ν ε (LogConcaveQuery): |μ.real B − ν.real B| ≤ ε for every measurable B; laws as Measure.map; reason: the same quantity, TV ≤ ε iff every measurable set is within ε
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 19, Theorem 3 (PDF p. 22)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Measurement

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory

namespace SampQueryLB.WarmSLC

theorem theorem_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {O : Type*} [MeasurableSpace O] [StandardBorelSpace O] (μO : Measure O)
    [IsProbabilityMeasure μO] {q : ℕ} (hq : 1 ≤ q) {m : Fin q → ℕ} (P : MeasProcess E O q m)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1 / 2)
    (hsep : ∀ (w : O) (z : Rec q m),
      ‖(P.localSpan w z).starProjection ∘L (P.farSpan w z).starProjection‖ ≤ ρ) :
    ∀ (β : Type) [MeasurableSpace β] (f : O × Rec q m → β), Measurable f →
      TVAtMost ((P.shLaw μO).map f) ((P.indLaw μO).map f) (3 / 2 * ρ * ∑ k, (m k : ℝ)) := by sorry

end SampQueryLB.WarmSLC
