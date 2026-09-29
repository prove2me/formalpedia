-- Prove2me | Theorems.Thm_TaoFivePrimes_local_L2_estimate
-- name    : TaoFivePrimes.local_L2_estimate
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T02:09:56.903985+00:00
-- url     : https://prove2.me/theorems/143bf587-a099-4a02-8844-f9cefc3a8e51
-- title:
--   Tao Lemma 4.6: the local $L^2$ estimate on a Farey system of major arcs
-- statement:
--   Let $Q,R\ge1$ and let
--
--   $$\Sigma:=\bigcup_{q_0\le Q}\ \bigcup_{a_0}\ \left\{\alpha\in\mathbb R/\mathbb Z:\ \left\|\alpha-\frac{a_0}{q_0}\right\|_{\mathbb R/\mathbb Z}<\frac{1}{2Q^2R^2}\right\}$$
--
--   be the union of the major arcs of radius $1/(2Q^2R^2)$ around the fractions of denominator at most $Q$. Let $f\ge0$ be an integrable function on $\mathbb R/\mathbb Z$ which obeys Montgomery's uncertainty inequality
--
--   $$\frac{\mu^2(q_1)}{\varphi(q_1)}\,f(\alpha)\ \le\ \sum_{\substack{a\ \mathrm{mod}\ q_1\\ (a,q_1)=1}} f\!\left(\alpha+\frac{a}{q_1}\right)\qquad(1\le q_1\le R,\ \alpha\in\mathbb R/\mathbb Z).$$
--
--   Then
--
--   $$\log R\int_\Sigma f(\alpha)\,d\alpha\ \le\ \left(\prod_{p\le Q}\frac{p}{p-1}\right)\int_{\mathbb R/\mathbb Z}f(\alpha)\,d\alpha,$$
--
--   where $\mu$ is the Möbius function, $\varphi$ the Euler totient, $d\alpha$ the probability Haar measure on $\mathbb R/\mathbb Z$, and $\|t\|_{\mathbb R/\mathbb Z}$ the distance to the nearest integer.
--
--   Applied to $f=|S_{\eta,q}(x,\cdot)|^2$ with $R\sharp\mid q$ — for which the Montgomery hypothesis is exactly Lemma 4.4 of the source and for which the total integral is at most $S_{\eta^2,q}(x,0)\log x$ by the global $L^2$ estimate — this is the source's local $L^2$ estimate
--
--   $$\int_\Sigma|S_{\eta,q}(x,\alpha)|^2\,d\alpha\le\left(\prod_{p\le Q}\frac{p}{p-1}\right)\frac{\log x}{\log R}\,S_{\eta^2,q}(x,0),$$
--
--   which removes almost the whole logarithmic loss of the global bound by restricting to major arcs. The mechanism is that the translates $\Sigma+a_1/q_1$, over reduced fractions $a_1/q_1$ with $Q$-rough denominator $q_1\le R$, are pairwise disjoint, so the Montgomery inequality can be averaged over them against the single global bound; the total weight of the translates is $\sum_{q_1\le R,\,(q_1,Q\sharp)=1}\mu^2(q_1)/\varphi(q_1)$, which is at least $\log R$ divided by the Mertens product.
--
--   **Formalization Note** The result is stated for an arbitrary nonnegative integrable $f$ satisfying the Montgomery inequality rather than for $|S_{\eta,q}(x,\cdot)|^2$ specifically; that inequality, the source's Lemma 4.4, is therefore carried as a hypothesis, and the conclusion is written as $\log R\cdot\int_\Sigma f\le(\cdots)\int f$ so that no division by $\log R$ occurs at $R=1$. The arcs are taken open rather than closed; the two versions of $\Sigma$ differ by a null set, and the source likewise only asserts that the translates are disjoint up to null sets. The inner union over $a_0$ runs over all residues $0\le a_0<q_0$ rather than the reduced ones, which gives the same set $\Sigma$ since an unreduced fraction reduces to one with a smaller denominator.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.6 (Local L^2 estimate), equation (4.7); the quoted Montgomery inequality is Lemma 4.4 there (Montgomery's uncertainty principle), and the bound G(R) >= log R is attributed there to van Lint-Richert and to Montgomery-Vaughan, Lemma 3

import Mathlib

open Finset MeasureTheory

theorem TaoFivePrimes.local_L2_estimate (Q R : ℕ) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (f : AddCircle (1 : ℝ) → ℝ) (hf0 : ∀ α, 0 ≤ f α)
    (hfi : MeasureTheory.Integrable f AddCircle.haarAddCircle)
    (hmup : ∀ q1 : ℕ, 0 < q1 → q1 ≤ R → ∀ α : AddCircle (1 : ℝ),
      ((ArithmeticFunction.moebius q1 : ℝ)) ^ 2 / (Nat.totient q1 : ℝ) * f α
        ≤ ∑ a ∈ (Finset.range q1).filter (fun a => Nat.Coprime a q1),
            f (α + (((a : ℝ) / q1 : ℝ) : AddCircle (1 : ℝ)))) :
    Real.log R *
        (∫ α in (⋃ q0 ∈ Finset.Icc 1 Q, ⋃ a0 ∈ Finset.range q0,
              Metric.ball ((((a0 : ℝ) / q0 : ℝ) : AddCircle (1 : ℝ)))
                (1 / (2 * (Q : ℝ) ^ 2 * (R : ℝ) ^ 2))),
            f α ∂AddCircle.haarAddCircle)
      ≤ (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)))
        * ∫ α, f α ∂AddCircle.haarAddCircle := by sorry
