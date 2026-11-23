-- Prove2me | Theorems.Thm_RossQC_Regions_Supplement_lemma_2_1_prime
-- name    : RossQC.Regions.Supplement.lemma_2_1_prime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:03:19.603567+00:00
-- url     : https://prove2.me/theorems/210fd9ff-7b16-4ac0-8c15-11332ea50b59
-- title:
--   Lemma 2.1′ — the average-cost relative value f is concave on the belief simplex
-- statement:
--   Consider the general model of Ross's §2: countably many underlying states, a stochastic transition matrix $(P_{ij})$, bounded costs $C_i,I_i,R_i$, and the belief simplex $S$. For a discount $b\in(0,1)$ let $V_b$ be the discounted optimal cost, fix a reference belief $P^0\in S$, and let $f_b(P)=V_b(P)-V_b(P^0)$.
--
--   Suppose the family $\{f_b(P):P\in S,\ b\in(0,1)\}$ is uniformly bounded and equicontinuous. Let $f$ be a function on beliefs such that, for some sequence $\beta_r\in(0,1)$ with $\beta_r\to1$,
--   $$
--   f(P)=\lim_{r\to\infty}f_{\beta_r}(P)\qquad\text{for every }P\in S.
--   $$
--   Then $f$ is concave on $S$: for $P^1,P^2\in S$ and $\lambda\in[0,1]$,
--   $$
--   f(\lambda P^1+(1-\lambda)P^2)\ \ge\ \lambda f(P^1)+(1-\lambda)f(P^2).
--   $$
--
--   In the paper $f$ is the relative value function of the average-cost optimality equation (2), supplied by the theorem quoted from Ross (1968); this lemma is the average-cost counterpart of Lemma 2.1 and the step on which Theorem 2.2′ rests.
--
--   **Formalization Note** The discounted cost $V_b$ is the base mission's $V_\beta$ (limit of value iteration) at discount $b$; the discount stored in the model plays no role. Equicontinuity is with respect to the $\ell^1$ distance on $S$.
--
--   Differences from the source:
--   - generalization: $f$ is the bounded function of the quoted theorem, satisfying (2) and both limits in (b) → $f$ is any function with the limit property $f=\lim_r f_{\beta_r}$ on $S$ along some $\beta_r\in(0,1)$, $\beta_r\to1$; reason: the paper's $f$ has this property by (b), so the statement specializes to the paper's $f$, and the paper derives the lemma "from (b) of the above and Lemma 2.1" only.
--   - reading: "equicontinuous", no metric named → equicontinuity at every point of $S$ for the $\ell^1$ distance $\sum_i|P_i-Q_i|$; reason: the paper specifies no metric; this makes the topology convention explicit without assuming continuity or changing the countable state domain; both conclusions follow already from pointwise limits of concave discounted values and (2).
--   - encoding: $V_\beta$ as the infimum over policies → $V_\beta$ as the limit of value iteration from $V^0=0$ (the base mission's definition) at discount $b$; reason: inherited published convention, justified on p. 589 by "$V^n_\beta(P)\to V_\beta(P)$".
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 589, Lemma 2.1′

import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_Supplement_AverageCost

namespace RossQC.Regions.Supplement

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 589, Lemma 2.1′: "If `{f_β(P)}` is uniformly bounded and
equicontinuous then `f(P)` is a concave function of `P`."

Under the standing hypotheses of §1–§2 (`Model.Valid`), for a reference belief `P⁰ ∈ S` such that
the relative values `f_b = V_b − V_b(P⁰)`, `b ∈ (0, 1)`, are uniformly bounded and equicontinuous on
`S`, every `f` that is a pointwise limit on `S` of `f_{β_r}` along some sequence `β_r ∈ (0, 1)`,
`β_r → 1` (clause (b) of the quoted Theorem) is concave on `S`.

**Formalization Note.** `f` is any function with the property (b) the paper's `f` has, so the
statement covers the paper's `f` whichever pair the quoted Theorem supplies. `M.β` plays no role:
only the discounts `b ∈ (0, 1)` of `withDiscount M b` enter. Equicontinuity uses
the `ℓ¹` distance on `S`, a metric not specified by the paper. -/
theorem lemma_2_1_prime {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid)
    (P₀ : ι → ℝ) (hP₀ : P₀ ∈ M.simplex) (hfam : UnifBddEquicont M P₀)
    (f : (ι → ℝ) → ℝ) (hf : IsRelValueLimit M P₀ f) :
    ConcaveOn ℝ M.simplex f := by sorry

end RossQC.Regions.Supplement
