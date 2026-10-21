-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_proposition_8
-- name    : TraceAdopt.LPReform.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:12.905217+00:00
-- url     : https://prove2.me/theorems/f9072637-2c08-4e03-85f8-1ef262d3c58c
-- title:
--   Proposition 8, p. 18 — formulations (5) and (10) are equivalent (bit ranges as in ILP (11))
-- statement:
--   Let $(T',\{X'_z\})$ be a rooted binary tree decomposition of $G'$ with partitions $\{J^i_z\}$, $\{I^j_z\}$ as in formulation (10), and let $\mathcal F_5$, $\mathcal F_{10}$ be the feasible regions of (5) and (10) on this decomposition. For every binary seed vector $s$,
--
--   $$\exists(\ell,u,\tilde u,v,\tilde v):\ (s,\ell,u,\tilde u,v,\tilde v)\in\mathcal F_{10}\quad\Longleftrightarrow\quad\exists\ell:\ (s,\ell)\in\mathcal F_5 .$$
--
--   Moreover, for every real cost vector $w$, if $(s^*,\ell^*,u^*,\tilde u^*,v^*,\tilde v^*)$ is an optimal solution of (10), then $S^*_0=\{i\in N_F:s^*_i=1\}$ fully activates the network and $\sum_iw_is^*_i=\mathrm{OPT}(w)$: $S^*_0$ solves MIN-SCTM.
--
--   This is the step that replaces the long covering constraints of (5) by partial sums along the tree decomposition without changing the feasible seed vectors.
--
--   **Formalization Note** Formulation (10) is the corrected one of the definition item: bit ranges $n_u=\lfloor\log_2c_{\max}\rfloor$, $n_v=\lfloor\log_2(\max_j\theta_j-1)\rfloor$ as required by the ILP (11) of the proof, $u$ and $v$ at the subtree roots in (10c), (10g), children inside the subtrees, distinct vertices in (10i), (10j). As printed, with the bit count (6), the statement is false: for $n=3$, $e_a=\{1,2\}$, $e_b=\{1,3\}$, $\theta\equiv2$, unit benefits, $c_1=2$, $c_2=c_3=1$ and the one-bag decomposition, (6) gives $n_u=0$, so $u_{1z}\le1$ and (10c) forces $s_1=1$, although $\{2,3\}$ fully activates the network. The partitions are arbitrary data with the stated properties (the proof on p. 40 uses only these). The feasibility correspondence is the one the proof establishes. The §3.1 standing assumptions are hypotheses.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 18, Proposition 8; pp. 39–40, formulation (10), ILP (11) and proof

import Definitions.Def_TraceAdopt_LPReform_BiLP5
import Definitions.Def_TraceAdopt_LPReform_BiLP10

namespace TraceAdopt.LPReform

/-- Proposition 8, p. 18 (with the bit ranges of the ILP (11) of its proof and the
root terms `u`, `v` in (10c), (10g)): on a rooted binary tree decomposition of `G′`
with partition data, formulations (10) and (5) have the same feasible seed vectors,
and an optimal solution of (10) gives a minimum-cost fully activating seed set. -/
theorem proposition_8 (I : Instance) (hI : I.Standing) {T : Type} [Fintype T] [DecidableEq T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
    (hX : IsRootedBinaryTD I t X' rt par) (hJ : IsPartitionData I X' J Ip) :
    (∀ s : Fin I.n → ℕ,
      (∃ ℓ u ut v vt, BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt) ↔
        ∃ ℓ, BiLP5Feasible I X' s ℓ) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
        (u ut : Fin I.n → T → Fin (nu I + 1) → ℕ)
        (v vt : Fin I.m → T → Fin (nv I + 1) → ℕ),
      BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt →
      (∀ (s' : Fin I.n → ℕ) (ℓ' : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
          (u' ut' : Fin I.n → T → Fin (nu I + 1) → ℕ)
          (v' vt' : Fin I.m → T → Fin (nv I + 1) → ℕ),
        BiLP10Feasible I X' rt par J Ip s' ℓ' u' ut' v' vt' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) := by sorry

end TraceAdopt.LPReform
