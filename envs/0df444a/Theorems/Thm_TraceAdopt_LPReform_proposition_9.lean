-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_proposition_9
-- name    : TraceAdopt.LPReform.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:38.03043+00:00
-- url     : https://prove2.me/theorems/d74a0d35-9555-430a-98e9-6205094207bd
-- title:
--   Proposition 9, p. 18 — the intersection graph of (10) has treewidth $O(\omega^{\prime 2}+\omega^\prime\log_2\vartheta_{\max})$
-- statement:
--   Let $\vartheta_{\max}=\max\{\max_ic_i,\ \max_j\theta_j-1\}$. There is one absolute constant $C>0$ such that the following holds for every instance satisfying the standing assumptions. Let $(T',\{X'_z\})$ be a rooted binary tree decomposition of the auxiliary graph $G'$ with every bag of size at most $\omega'+1$, and let $\{J^i_z\}$, $\{I^j_z\}$ be partitions as in formulation (10). Then the intersection graph of (10) built on these data has treewidth at most
--
--   $$C(\omega'+1)^2+C(\omega'+1)\bigl(\lfloor\log_2\vartheta_{\max}\rfloor+1\bigr).$$
--
--   That is, the treewidth is $O(\omega'^2+\omega'\log_2\vartheta_{\max})$, where $\omega'$ is the width of the decomposition of $G'$. Combined with Proposition 4, this is what makes the LP reformulation of formulation (10) small.
--
--   **Formalization Note** The constant $C$ is chosen before the instance and the decomposition. The shifts by one make the bound meaningful for $\omega'=0$ and $\vartheta_{\max}=1$; under the standing assumptions $\vartheta_{\max}\ge1$. "$\omega'$ is the treewidth of $G'$" is read as "the given decomposition of $G'$ has width at most $\omega'$", the form used in the proof on p. 41. The proof's explicit bag count $\omega'^2+4\max\{n_u,n_v\}\omega'$ is not used. Formulation (10) is the corrected one of the definition item.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 18, Proposition 9; p. 41, proof

import Definitions.Def_TraceAdopt_LPReform_BiLP10Graph

namespace TraceAdopt.LPReform

/-- Proposition 9, p. 18: the intersection graph of (10), built on a rooted binary
tree decomposition of `G′` of width at most `ω′`, has treewidth
`O(ω′² + ω′ log₂ ϑ_max)`, with one absolute constant `C`. -/
theorem proposition_9 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (I : Instance), I.Standing →
      ∀ {T : Type} [Fintype T] [DecidableEq T]
        (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
        (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
        (ω' : ℕ),
        IsRootedBinaryTD I t X' rt par → IsPartitionData I X' J Ip →
        (∀ z, (X' z).card ≤ ω' + 1) →
        RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph10 I X' rt par J Ip)
          (C * (ω' + 1) ^ 2 + C * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1)) := by sorry

end TraceAdopt.LPReform
