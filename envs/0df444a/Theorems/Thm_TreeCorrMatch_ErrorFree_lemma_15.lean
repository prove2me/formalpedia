-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_15
-- name    : TreeCorrMatch.ErrorFree.lemma_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:25:37.15218+00:00
-- url     : https://prove2.me/theorems/b305a7a8-bf7c-4f3d-87db-f96cc0c65d56
-- title:
--   Lemma 15 — the depth-$d$ neighbourhoods of $u$ and $\tilde u$ couple with a correlated Galton–Watson pair, failure $O(n^{-1/2})$
-- statement:
--   Let $(G,\tilde G)\sim\mathrm{CER}(n,\lambda,s)$ with $\lambda_n\to\infty$, $\lambda_n\le(\log n)^K$ for some $K$, and a constant $s\in(\sqrt{C_{\mathrm{Otter}}},1]$; let $\gamma\in(0,1)$. For an integer $d\ge0$ with $d\le(\log n)^\gamma$ and a node $u$, let $T$ be the $d$-hop neighbourhood of $u$ in $G$ rooted at $u$ if it is a tree, and the empty tree otherwise, and let $\tilde T$ be defined in the same way for $\tilde u=\pi(u)$ in $\tilde G$. Then there is a coupling of $(T,\tilde T)$ and $(H,\tilde H)\sim P$ with
--
--   $$\mathbb P\big([T]=[H_d],\ [\tilde T]=[\tilde H_d]\big)=1-O(n^{-1/2}),$$
--
--   with a constant in $O(\cdot)$ independent of $n$, $d$ and $u$.
--
--   The coupling transfers the power of the test (Theorem 3) from correlated Galton–Watson trees to true pairs of nodes (Lemma 8).
--
--   **Formalization Note** The coupling is a probability mass function on pairs (classes of $(T,\tilde T)$, with `none` for an empty tree; classes of $(H_d,\tilde H_d)$) whose marginals are the two laws.
--
--   Differences from the source:
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: a coupling between (T, T̃) and (H, H̃) ∼ P, and the event [T] = [H_d], [T̃] = [H̃_d] → a coupling (PMF) of the laws of ([T], [T̃]) and ([H_d], [H̃_d]); reason: the event depends only on these classes; on countable spaces a coupling of the classes lifts to one of the objects
--   - reading: d ≤ (log n)^γ for some constant γ ∈ (0, 1), 1 − O(n^{-1/2}) → ∃ C, for all large n, for every d ≤ (log n)^γ and every u: coupling probability ≥ 1 − C n^{-1/2}; reason: the constant is independent of n, as the O(·) requires, and the proof's bound is uniform in d and u
--   - encoding: CER(n, λ, s) with parent edge probability λ/(ns), λ ∈ (0, ns] → parent edge probability clamped to [0, 1]; reason: the clamp changes only the finitely many n with λ_n > ns and no limit
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
--   - encoding: node set [n] → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 45, Lemma 15 and the paragraph before it (PDF p. 47)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_CER
import Definitions.Def_TreeCorrMatch_ErrorFree_LocalTree

open Filter Topology

namespace TreeCorrMatch.ErrorFree

theorem lemma_15 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ Real.log n ^ γ → ∀ u : Fin n,
      ∃ cpl : PMF ((Option UTree × Option UTree) × (UTree × UTree)),
        (∀ a : Option UTree × Option UTree, cpl.map Prod.fst a =
          ENNReal.ofReal (cerProb n (lam n) s (fun o =>
            ((localTree o.1 none u d ⊤).map cls, (localTree o.2.1 none (o.2.2 u) d ⊤).map cls) = a))) ∧
        cpl.map Prod.snd = (corrPairLaw (lam n) s d).map (fun p => (cls p.1, cls p.2)) ∧
        1 - C * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
          (cpl.toOuterMeasure {z | z.1 = (some z.2.1, some z.2.2)}).toReal := by sorry

end TreeCorrMatch.ErrorFree
