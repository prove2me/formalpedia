-- Prove2me | Theorems.Thm_QCircMITM_Search_main_result
-- name    : QCircMITM.Search.main_result
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:30.481735+00:00
-- url     : https://prove2.me/theorems/7dd0f291-3166-4e15-a76a-20d469d0a8b1
-- title:
--   Main result, §2 p. 4 / §3 pp. 5–7 — MITM-factor decides depth ≤ 2⌈l/2⌉, returns a minimal-depth circuit, cost ≤ 8|V|^⌈l/2⌉ log₂|V|^⌈l/2⌉ (corrected)
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of $n$-qubit unitaries, standing for the set $\mathcal V_{n,\mathcal G}$ of depth-one circuits over an instruction set $\mathcal G$, and let $S_d$ be the set of unitaries implementable over $V$ in depth $d$. Let $U \in U(2^n)$, $l \ge 0$, and write $h = \lceil l/2\rceil$. Run MITM-factor$(\mathcal G, U, l)$.
--
--   1. **Decision.** It returns nothing if and only if $U$ has no circuit over $V$ of any depth $d$ with $1 \le d \le 2h$:
--   $$\text{MITM-factor}(\mathcal G,U,l) = \text{none} \iff U \notin S_1 \cup S_2 \cup \cdots \cup S_{2\lceil l/2\rceil}.$$
--   2. **Even $l$.** In particular, for even $l$, it returns nothing if and only if $U$ has no circuit of depth $d$ with $1 \le d \le l$.
--   3. **Minimality.** If it returns a circuit $c$, then every layer of $c$ lies in $V$, $c$ implements $U$, $1 \le |c| \le 2h$, and $|c| \le |c'|$ for every circuit $c'$ over $V$ of positive depth implementing $U$.
--   4. **Cost.** If $|V| \ge 2$, its counted cost (generation, sorting and searching, summed over the iterations it executes) satisfies
--   $$\mathrm{cost}(U,l) \le 8\,|V|^{\lceil l/2\rceil}\log_2\!\big(|V|^{\lceil l/2\rceil}\big).$$
--
--   This is the paper's main result: MITM-factor decides whether $U$ can be implemented in depth at most $l$ in time $O\big(|\mathcal V_{n,\mathcal G}|^{\lceil l/2\rceil}\log(|\mathcal V_{n,\mathcal G}|^{\lceil l/2\rceil})\big)$, and when it can, it returns a circuit of minimal depth. It does so while generating only circuits of depth at most $\lceil l/2\rceil$, the square root of the brute-force $|\mathcal V_{n,\mathcal G}|^l$.
--
--   **Formalization Note.** The layer set $V$ is an arbitrary finite set of unitaries; the paper's argument uses nothing else about $\mathcal V_{n,\mathcal G}$. Three corrections, all forced by the pseudocode on p. 6. (i) For odd $l$ the last iteration also tests depth $l+1$, so the decided range is $1 \le d \le 2\lceil l/2\rceil$; for even $l$ this is the printed range (clause 2). (ii) Depth $0$ is never tested, so minimality is among circuits of positive depth (this matters only for $U = I$). (iii) The running time is a counted cost: per iteration $i$, $|V||S_{i-1}|$ for generating $S_i$, $|S_i|\log_2|S_i|$ for sorting it, and $(|S_{i-1}|+|S_i|)\log_2|S_i|$ for the lookups, built from the sets the run actually generates. The $O$ is made explicit with the constant $8$: each iteration costs at most $4|V|^i\log_2|V|^h$, and $\sum_{i\le h}|V|^i \le 2|V|^h$ for $|V| \ge 2$. The hypothesis $|V| \ge 2$ is needed because $\log_2 1 = 0$. Logarithms are `Real.logb 2`, and $\lceil l/2\rceil$ is `(l + 1) / 2`.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 4 (§2, main result) and pp. 5–7 (§3: Lemma 1, MITM-factor pseudocode and its analysis)

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem main_result {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    (mitmFactor V U l = none ↔ ∀ d : ℕ, 1 ≤ d → d ≤ 2 * ((l + 1) / 2) → U ∉ S V d) ∧
    (Even l → (mitmFactor V U l = none ↔ ∀ d : ℕ, 1 ≤ d → d ≤ l → U ∉ S V d)) ∧
    (∀ c, mitmFactor V U l = some c →
        (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧ 1 ≤ c.length ∧ c.length ≤ 2 * ((l + 1) / 2) ∧
        ∀ c' : List (Unitary n), (∀ W ∈ c', W ∈ V) → c'.prod = U → 1 ≤ c'.length →
          c.length ≤ c'.length) ∧
    (2 ≤ V.card →
      mitmCost V U l ≤
        8 * (V.card : ℝ) ^ ((l + 1) / 2) * Real.logb 2 ((V.card : ℝ) ^ ((l + 1) / 2))) := by sorry

end QCircMITM.Search
