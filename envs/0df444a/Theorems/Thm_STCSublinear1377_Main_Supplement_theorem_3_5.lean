-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_theorem_3_5
-- name    : STCSublinear1377.Main.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:25:55.228477+00:00
-- url     : https://prove2.me/theorems/4aaf9e17-c97f-4502-80bd-a1adfee82165
-- title:
--   Theorem 3.5 — One connected partition controlling all small cuts, constants 2 and 4
-- statement:
--   Let $F$ be a connected graph with positive integer edge weights, $N=|V_F|$ vertices and total edge weight $M$, and let $\emptyset\ne U\subsetneq V_F$. For a partition $\mathcal P$ of $U$ and $C\subseteq U$ let $x_{\mathcal P}(C)$ be the total weight of edges with both ends in $C$ lying in different parts of $\mathcal P$. There is an absolute constant $\gamma_0>0$ such that for every $\gamma\ge\gamma_0$, with
--
--   $$\beta=\gamma\log^{3/2}(N+M),\qquad B_0=\max\{d,\lceil\beta b_0\rceil\},$$
--
--   and every $r>0$, some randomized algorithm running in time polynomial in $N+M$ does the following for all real $d,b_0$ such that every vertex of $U$ has degree at most $d$: it always outputs a partition $\mathcal P$ of $U$ into connected sets, and with probability at least $1-(N+M)^{-r}$ the same partition satisfies, simultaneously,
--
--   $$b_F(A)\le 2B_0\quad\forall A\in\mathcal P,\tag{3.5}$$
--   $$x_{\mathcal P}(C)\le 4\beta\,b_F(C)\quad\forall C\subseteq U\ \text{with}\ b_F(C)\le b_0.\tag{3.6}$$
--
--   The theorem is the partition step of Lemma 3.7, which builds the spanning trees of the main algorithm.
--
--   Differences from the source:
--   - generalization: F a connected positive-integer-weighted quotient of a subgraph of the original graph G → any connected positive-integer-weighted graph, with running time charged to N + M by writing the total weight in unary; reason: the quotient property is used only to bound M ≤ |E(G)| in the running time; every source graph F is covered and for it N + M is polynomial in |G|
--   - encoding: real parameters d and b₀ → the machine receives ⌊d⌋ and max(0, ⌈βb₀⌉); the conclusion uses the real d, b₀, β and B₀; reason: integer boundaries satisfy b ≤ B₀ iff b ≤ max(⌊d⌋, ⌈βb₀⌉), and ⌊d⌋ ≥ 1 since some vertex of U has an edge leaving U
--   - reading: for a sufficiently large constant γ > 0, a randomized polynomial-time algorithm constructs P such that (3.5), (3.6) → ∃ γ₀ > 0 ∀ γ ≥ γ₀ ∀ r > 0 a machine: every tape gives a partition of U into connected sets, and on one event of probability ≥ 1 − (N + M)^{−r} both (3.5) and (3.6) hold for all eligible C; reason: swaps replace parts by connected components, so every run yields connected parts; the high-probability statement is the amplification and union bound on p.13
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem 3.5, (3.5)–(3.6), PDF/printed p.11; proof pp.11–13

import Definitions.Def_STCSublinear1377_Main_Supplement_Quota
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Theorem 3.5: one absolute threshold `γ₀`; for every `γ ≥ γ₀` both (3.5) and (3.6), the latter
for all eligible `C` at once, hold on one event. Real parameters reach the machine as
`⌊d⌋` and `⌈β b₀⌉`; the total weight `M` is charged in unary. -/
theorem theorem_3_5 :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ → ∀ r : ℝ, 0 < r → ∃ a : RandomDataMachine,
      ∀ n : ℕ, ∀ f : WeightedGraph n,
        f.vertices = Finset.univ → f.positive → f.integral → f.connected →
        ∀ U : Finset (Fin n), U.Nonempty → U ≠ Finset.univ →
        ∀ d b₀ : ℝ, (∀ u ∈ U, f.degree u ≤ d) →
        let M := f.totalWeight
        let β := γ * Real.rpow (Real.log ((n : ℝ) + M)) (3 / 2 : ℝ)
        let B₀ := max d ((⌈β * b₀⌉ : ℤ) : ℝ)
        let input := unaryGraphBits f ++ setBits U ++ natBits (Int.toNat ⌊d⌋) ++
          natBits (Int.toNat ⌈β * b₀⌉)
        (∀ tape : Fin (a.tapeLength input) → Bool, ∃ lab : Fin n → Fin n,
          a.output input tape = labelBits lab ∧ ∀ A ∈ labelParts U lab, f.connectedSet A) ∧
        dataProbability a input (fun out => ∃ lab : Fin n → Fin n,
          out = labelBits lab ∧ (∀ A ∈ labelParts U lab, f.connectedSet A) ∧
          (∀ A ∈ labelParts U lab, f.boundary A ≤ 2 * B₀) ∧
          (∀ C : Finset (Fin n), C ⊆ U → f.boundary C ≤ b₀ →
            crossWeight f lab C ≤ 4 * β * f.boundary C)) ≥
          1 - Real.rpow ((n : ℝ) + M) (-r) := by sorry

end STCSublinear1377.Main.Supplement
