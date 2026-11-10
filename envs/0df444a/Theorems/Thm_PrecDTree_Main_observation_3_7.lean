-- Prove2me | Theorems.Thm_PrecDTree_Main_observation_3_7
-- name    : PrecDTree.Main.observation_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:52:50.380581+00:00
-- url     : https://prove2.me/theorems/4d85692c-130e-4390-9529-22451d3ec2e3
-- title:
--   Observation 3.7 — the path D_C of one call of Algorithm 1 costs at most α · |sepc(I)|
-- statement:
--   Consider one call of Algorithm 1 on a PCWCDT instance $I=(H,T,\preceq)$ in which FindCover is an $(\alpha,\beta)$-approximation for f-PCSC ($\beta\ge1$): its output $\mathcal C$ on $(U_\xi,\xi(T),\preceq_\xi,f=1/4)$ is precedence-closed, covers at least $\frac14|U_\xi|/\beta$ hypotheses and has $|\mathcal C|\le\alpha\cdot\mathrm{OPT}$. The tests of $\mathcal C$ are performed in a topological order $L$, and $D_{\mathcal C}$ is the path of the call that follows replies not reaching the recursion threshold $\frac{5\beta-1}{5\beta}|H|$. Then, for every optimal tree $D$ for $I$ and every sepcover of it,
--   $$\mathrm{cost}_W(D_{\mathcal C})\ \le\ \alpha\cdot|\mathrm{sepc}(I)| .$$
--   This is the per-call cost bound that Theorem 3.8 sums over the $O(\log n)$ levels of the recursion.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: I = (H, T, ⪯) is an instance of the problem → hypotheses: ⪯ is a partial order (IsPartialOrderRel), H is nonempty, and every two distinct hypotheses are separated by some test (Identifiable); reason: the standing assumptions of §2 and the domain of the problem: without separation no decision tree exists and OPT is undefined (the proof of Lemma 3.4 uses it explicitly)
--   - reading: sepc(I) = sepc(D) for an optimal D, ties broken arbitrarily (Definition 3.3) → the conclusion holds for every optimal precedence-closed tree D and every sepcover S of D (IsSepcover, every admissible tie-breaking); reason: 'ties broken arbitrarily' means the statement must hold whatever the choice
--   - generalization: FindCover is a (polynomial-time) (α, β)-approximation algorithm for f-PCSC and C its output → any cover C meeting the bicriteria ratio (α, β) on the call's ξ-instance (IsBicriteria), with α, β real and β ≥ 1; reason: the observation uses only the guarantee of FindCover's output; the output of an (α, β)-approximation algorithm is one such C
--   - encoding: 'Order C topologically' and the path D_C of the current call → a list L with IsTopoOrder le C L, and cost_W(D_C) = callPathCost T Hs β Hs L; reason: the call performs the tests of C in the order L; callPathCost counts the test nodes of the path that follows replies above the threshold
--   - reading: β of the (α, β) ratio → hypothesis 1 ≤ β; reason: the paper's standing convention for the bicriteria ratio (p. 6: 'for β ≥ 1')
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 7, Observation 3.7

import Mathlib
import Definitions.Def_PrecDTree_Main_Sepcover
import Definitions.Def_PrecDTree_Main_Xi

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Observation 3.7** (p. 7). In a call of Algorithm 1 on `I = (H, T, ⪯)` whose FindCover returns
a cover `C` meeting the bicriteria ratio `(α, β)` on `(U_ξ, ξ(T), ⪯_ξ, f = 1/4)`, performed in a
topological order `L`, the path `D_C` of the call satisfies `cost_W(D_C) ≤ α · |sepc(I)|`. -/
theorem observation_3_7 {m : ℕ} {H : Type} [DecidableEq H] (le : Fin m → Fin m → Prop)
    (T : Fin m → H → ℕ) (Hs : Finset H) (hle : IsPartialOrderRel le) (hid : Identifiable T Hs)
    (hne : Hs.Nonempty) (α β : ℝ) (hβ : 1 ≤ β) (C : Finset (Fin m))
    (hC : IsBicriteria le (xi T Hs) (1 / 4 : ℝ) α β C) (L : List (Fin m))
    (hL : IsTopoOrder le C L) (D : DTree m H) (hD : IsOptimalW le T Hs D) (S : List (Fin m))
    (hS : IsSepcover T Hs D S) :
    (callPathCost T Hs β Hs L : ℝ) ≤ α * (S.length : ℝ) := by sorry

end PrecDTree.Main
