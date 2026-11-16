-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_5_2
-- name    : ShiAuthentication.BA.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:27:45.981627+00:00
-- url     : https://prove2.me/theorems/33aab3ea-ea7f-41ae-8b28-a3b120dadbc1
-- title:
--   Lemma 5.2 — broadcast reduction to sparse agreement
-- statement:
--   Let $n\ge3$, $1\le t<n$, and $1\le s\le t$ with $n-s>2(t-s)$; let $S$ be the designated sender. Let $K_{\mathrm{reg}}\ni S$ be a set of $s$ parties and let $U_{\mathrm{res}}=P\setminus K_{\mathrm{reg}}$ (its $n-s$ parties listed injectively). If a graph $G_{\mathrm{res}}$ on $U_{\mathrm{res}}$ supports Byzantine agreement with fault bound $t-s$, then the graph $G$ obtained by adding the $s(n-1)$ authentication edges out of $K_{\mathrm{reg}}$ (every $x\in K_{\mathrm{reg}}$ is authenticated to every other party) supports $\mathrm{BB}(G,S,t)$, and $|E(G)|=s(n-1)+|E(G_{\mathrm{res}})|$. Consequently
--   $$A_{BB}(n,t)\ \le \min_{\substack{1\le s\le t\\ n-s>2(t-s)}}\big\{s(n-1)+A_{BA}(n-s,t-s)\big\}.\tag{3}$$
--
--   Registering a few parties globally thus reduces broadcast to Byzantine agreement on the remaining parties with a reduced fault bound; this yields the upper bounds of Corollary 5.3 and Main Theorem 3.
--
--   Differences from the source:
--   - encoding: BB(G, S, t) feasible → BBPossible .publicGraph t G S; reason: Definition 3.1 in the model of §3.1, where the authentication graph G is public
--   - encoding: A_BB(n, t) → ABB t S, stated for every designated sender S; reason: Definition 3.3 minimizes over setups for broadcast from a designated sender; the bound is claimed for every sender
--   - generalization: G_res supports BA with fault bound t − s (public-graph model of §3.1); A_BA(n − s, t − s) → BAPossible mode (t − s) G_res for an arbitrary knowledge setting mode, and A_BA in that setting; reason: the statement is claimed for every setting; the public-graph instance is the source's claim
--   - encoding: the minimum over admissible s in (3) → for the fixed admissible s of the statement, A_BB(n, t) ≤ s(n − 1) + A_BA(n − s, t − s); reason: the theorem is quantified over every admissible s, which is equivalent to the bound by the minimum
--   - encoding: using the s(n − 1) authentication edges out of K_reg gives a graph G → G = registeredGraph K e G_res, with the edge count s(n − 1) + |E(G_res)| stated; reason: makes the setup and its cost, used for (3), explicit
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 5.2 and Protocol 4, p. 25

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 5.2 (Broadcast reduction)**, p. 25. Let `n ≥ 3`, `1 ≤ t < n`, `1 ≤ s ≤ t` with
`n − s > 2(t − s)`, and let `S` be the designated sender. Let `K_reg ∋ S` be a set of `s` parties
and `e` an injective listing of the `n − s` parties of `U_res = P \ K_reg`. If a graph `G_res` on
`U_res` supports Byzantine agreement with fault bound `t − s` (in either knowledge setting), then
adding the `s(n − 1)` authentication edges out of `K_reg` gives a graph `G` (`registeredGraph`)
supporting `BB(G, S, t)`, and `G` has `s(n − 1) + |E(G_res)|` edges. Consequently
`A_BB(n, t) ≤ s(n − 1) + A_BA(n − s, t − s)` for this `s`; ranging over all admissible `s` this is
inequality (3), `A_BB(n, t) ≤ min_{1≤s≤t, n−s>2(t−s)} {s(n − 1) + A_BA(n − s, t − s)}`. -/
theorem lemma_5_2 (n t s : ℕ) (hn : 3 ≤ n) (ht1 : 1 ≤ t) (htn : t < n) (hs1 : 1 ≤ s)
    (hst : s ≤ t) (hres : 2 * (t - s) < n - s) (S : Fin n) :
    (∀ (K : Finset (Fin n)) (e : Fin (n - s) ↪ Fin n) (Gres : AuthGraph (n - s))
        (mode : Knowledge),
      S ∈ K → K.card = s → (∀ i, e i ∉ K) → BAPossible mode (t - s) Gres →
      BBPossible .publicGraph t (registeredGraph K e Gres) S ∧
      edgeCount (registeredGraph K e Gres) = s * (n - 1) + edgeCount Gres) ∧
    ∀ mode : Knowledge, ABB t S ≤ ((s * (n - 1) : ℕ) : ℕ∞) + ABA mode (n - s) (t - s) := by sorry

end ShiAuthentication.BA.Supplement
