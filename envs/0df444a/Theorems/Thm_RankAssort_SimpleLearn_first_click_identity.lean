-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_first_click_identity
-- name    : RankAssort.SimpleLearn.first_click_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:38.60275+00:00
-- url     : https://prove2.me/theorems/8afd9d12-bb3b-415f-a585-533be4b02de5
-- title:
--   Proof of Lemma 1, p. 53 — with no prior click the next click is Bernoulli(pᵢ): the hook probability equals the coupled first-click probability and 1 − ∏(1 − p)
-- statement:
--   Fix a customer type $(p,f,k)$ and a ranking $\pi$ (more generally any duplicate-free list of products), and let $w = \min(k, |\pi|)$ be the browsed window. Then the probability that the customer is hooked under the sequential click law with bias equals
--
--   1. the probability, under the coupled first-click law (one Bernoulli$(p_i)$ like-variable $L_i$ per product), that some product in the window is liked:
--   $$
--   \Pr[H(\pi) = 1 \mid (p,f,k)] = \Pr\bigl[\exists j \le w:\ L_{\pi^{-1}(j)} = 1\bigr];
--   $$
--   2. the closed form
--   $$
--   \Pr[H(\pi) = 1 \mid (p,f,k)] = 1 - \prod_{j=1}^{w}\bigl(1 - p_{\pi^{-1}(j)}\bigr).
--   $$
--
--   This is the content of the paper's remark that, conditional on no prior clicks, a click on product $i$ is a Bernoulli variable with probability $p_i + f_i(\emptyset) = p_i$. It ties the coupled first-click law used in the proofs to the model: every statement phrased with the coupled law is a statement about the sequential click law with bias.
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. The first part is `hookProb θ l = coupledProb θ (…)`, the second the product formula over the window `Fin (window θ l)`. The hypothesis that the list has no duplicates is needed: the coupled law gives every copy of a product the same coin.
--
--   Differences from the source:
--   - generalization: any ranking π → any duplicate-free list l of products (a ranking or a prefix of one); reason: a full ranking is the case length l = n
--   - reading: conditional on no prior clicks, the click on product i is Bernoulli(pᵢ + fᵢ(∅)) = Bernoulli(pᵢ) → the conditional hook probability equals the coupled first-click probability that some window product is liked, and equals 1 − ∏ over the window of (1 − p); reason: the remark is used in the proof of Lemma 1 exactly to replace the sequential law by these forms; the per-click statement is their one-step content
--   - encoding: conditional on the customer's type (p, f, k) → a statement for a fixed θ : CustomerType n; reason: the same conditioning
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 53, proof of Lemma 1, 'For any ranking π, we know that conditional on no prior clicks …'

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model

namespace RankAssort.SimpleLearn
theorem first_click_identity {n : ℕ} (θ : CustomerType n) (l : List (Fin n)) (hl : l.Nodup) :
    hookProb θ l =
        coupledProb θ (fun L => ∃ j, ∃ hj : j < l.length, j < θ.k ∧ L (l.get ⟨j, hj⟩) = true) ∧
      hookProb θ l = 1 - ∏ j : Fin (window θ l), (1 - θ.p (windowGet θ l j)) := by sorry
end RankAssort.SimpleLearn
