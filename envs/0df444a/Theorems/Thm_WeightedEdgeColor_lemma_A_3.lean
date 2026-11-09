-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_A_3
-- name    : WeightedEdgeColor.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:44:56.994487+00:00
-- url     : https://prove2.me/theorems/769ad18c-ec07-4461-a8e5-05974b9e30f9
-- title:
--   Lemma A.3 — one option per job with additive error $2\tau$ in every capacity constraint
-- statement:
--   Suppose each job $j$ has a probability distribution $p_j$ over finitely many options. Each option uses a nonnegative amount from at most two capacity constraints, and each amount is at most $\tau$. For a constraint $q$ let
--   $$
--   b_q=\sum_j\sum_o p_j(o)\,\mathrm{amt}_j(o,q)
--   $$
--   be the expected amount used in $q$. Then there is a choice $\sigma(j)$ of one option per job such that for every constraint $q$
--   $$
--   \sum_j \mathrm{amt}_j(\sigma(j),q)\le b_q+2\tau .
--   $$
--
--   In the paper jobs are small edges, an option is a color together with places at the two endpoints, and the lemma rounds the small-edge options after the large edges are matched.
--
--   **Formalization Note** There are finitely many jobs; the set of constraints is arbitrary. Each option's amounts vanish outside a set of at most two constraints.
--
--   Differences from the source:
--   - reading: "each amount is at most $\tau$" → in addition $\tau\ge0$; reason: $\tau$ bounds nonnegative amounts; without it the case with no jobs and $\tau<0$ would make the printed conclusion $0\le2\tau$ false
--   - reading: the number of jobs is unstated → finitely many jobs; reason: the proof is linear algebra on finitely many variables, and $b_q$ is a finite sum
--   - reading: the set of capacity constraints is unstated → an arbitrary type of constraints; reason: each constraint's load is a finite sum over the jobs, so no finiteness is needed, and a finite set of constraints is a special case
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Lemma A.3, p.25

import Mathlib

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Lemma A.3 (one option per job).

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Lemma A.3, p.25.

**Formalization Note.** Jobs form a finite type `J`; job `j` has finitely many options `O j`
with probabilities `p j`. Capacity constraints form an arbitrary type `Q`; option `o` of job `j`
uses `amt j o q ≥ 0` from constraint `q`, nonzero for at most two constraints, each at most
`τ`. The expected amount is `b_q = ∑_j ∑_o p_j(o) amt_j(o, q)`. `τ ≥ 0` is assumed: it bounds
nonnegative amounts (with no jobs and `τ < 0` the printed conclusion `0 ≤ 2τ` would fail). -/
theorem lemma_A_3 (J Q : Type) [Fintype J] (O : J → Type) [∀ j, Fintype (O j)]
    (p : ∀ j, O j → ℝ) (amt : ∀ j, O j → Q → ℝ) (τ : ℝ)
    (hp : ∀ j o, 0 ≤ p j o) (hp1 : ∀ j, ∑ o, p j o = 1)
    (hamt : ∀ j o q, 0 ≤ amt j o q ∧ amt j o q ≤ τ)
    (htwo : ∀ j o, ∃ s : Finset Q, s.card ≤ 2 ∧ ∀ q ∉ s, amt j o q = 0)
    (hτ : 0 ≤ τ) :
    ∃ σ : ∀ j, O j, ∀ q, ∑ j, amt j (σ j) q ≤ (∑ j, ∑ o, p j o * amt j o q) + 2 * τ := by sorry

end WeightedEdgeColor
