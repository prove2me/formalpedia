-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_14
-- name    : TreeCorrMatch.ErrorFree.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:25:42.009571+00:00
-- url     : https://prove2.me/theorems/ad8954b5-638a-4e59-81ea-47b9c0d52023
-- title:
--   Lemma 14 — node-disjoint local trees in CER vs the independent pair $Q$: ratio at most $\exp(\frac\lambda n((|V(t)|+1)|V(t)|+|V(\tilde t)|(1+|V(t)|+|V(\tilde t)|)))$
-- statement:
--   Let $(G,\tilde G)\sim\mathrm{CER}(n,\lambda,s)$ with $s\in(0,1]$ and $0<\lambda\le ns$, and let $d\ge0$. For nodes $u\ne w$ let $T$ be the local tree rooted at $w$ in $G\setminus u$ of depth up to $d$ (no degree cutoff; empty unless the depth-$d$ neighbourhood of $w$ in $G$ is a tree), and for nodes $\tilde v\ne\tilde x$ let $\tilde T$ be the local tree rooted at $\tilde x$ in $\tilde G\setminus\tilde v$. For every pair of rooted unlabeled trees $(t,\tilde t)$ of depth at most $d$,
--
--   $$\mathbb P\big(\{[T]=t\}\cap\{[\tilde T]=\tilde t\}\cap\{\bar V(T)\cap\bar V(\tilde T)=\emptyset\}\big)\le \exp\Big(\frac\lambda n\big((|V(t)|+1)|V(t)|+|V(\tilde t)|(1+|V(t)|+|V(\tilde t)|)\big)\Big)\,Q\big([H_d]=t,[\tilde H_d]=\tilde t\big).$$
--
--   Node-disjoint local trees of the two graphs are thus almost distributed as an independent Galton–Watson pair, which transfers the type-I error of the test to the graphs.
--
--   Differences from the source:
--   - encoding: the ratio P(…)/Q([H_d] = t, [H̃_d] = t̃) ≤ exp(…) → P(…) ≤ exp(…) · Q(…); reason: Q > 0 for every pair of trees of depth ≤ d, so the forms are equivalent
--   - encoding: (t, t̃) ∈ Z × Z of depth within d → ordered representatives t, t' of depth ≤ d, compared through cls; reason: every unlabeled tree has an ordered representative
--   - encoding: pairs (u, w) ∈ V × V and (ṽ, x̃) ∈ Ṽ × Ṽ → w ≠ u and x̃ ≠ ṽ; reason: the local tree 'rooted at w in G ∖ u' is undefined for w = u
--   - encoding: CER(n, λ, s), λ ∈ (0, ns], s ∈ (0, 1] → hypotheses 0 < s ≤ 1, 0 < λ ≤ n s; reason: the model's parameter range, stated in §1
--   - encoding: node set [n] → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 41, Lemma 14 and the paragraph before it (PDF p. 43)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_CER
import Definitions.Def_TreeCorrMatch_ErrorFree_LocalTree

namespace TreeCorrMatch.ErrorFree

theorem lemma_14 (n : ℕ) (lam s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (hlam0 : 0 < lam)
    (hlamn : lam ≤ n * s) (d : ℕ) (u w v x : Fin n) (hwu : w ≠ u) (hxv : x ≠ v) (t t' : OTree)
    (ht : t.depth ≤ d) (ht' : t'.depth ≤ d) :
    cerProb n lam s (fun o =>
        (∃ T, localTree o.1 (some u) w d ⊤ = some T ∧ cls T = cls t) ∧
        (∃ T', localTree o.2.1 (some v) x d ⊤ = some T' ∧ cls T' = cls t') ∧
        Disjoint (localVerts o.1 (some u) w d ⊤) (o.2.2 ⁻¹' localVerts o.2.1 (some v) x d ⊤)) ≤
      Real.exp (lam / n * (((t.size : ℝ) + 1) * t.size + t'.size * (1 + t.size + t'.size))) *
        classPairProb (indepPairLaw lam d) (cls t) (cls t') := by sorry

end TreeCorrMatch.ErrorFree
