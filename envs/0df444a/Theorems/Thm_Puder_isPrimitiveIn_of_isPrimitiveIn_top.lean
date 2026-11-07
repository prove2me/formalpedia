-- Prove2me | Theorems.Thm_Puder_isPrimitiveIn_of_isPrimitiveIn_top
-- name    : Puder.isPrimitiveIn_of_isPrimitiveIn_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:26.587142+00:00
-- url     : https://prove2.me/theorems/75ae5658-4bac-4841-8644-63ab1f0b7c0f
-- title:
--   Puder, p. 8 (Puder 2014, Claim 2.5) — a word primitive in F_d is primitive in every subgroup containing it
-- statement:
--   Let $w \in \mathbf F_d$ (`FreeGroup (Fin d)`) be primitive in $\mathbf F_d$, that is, a member of some basis (free generating set) of $\mathbf F_d$, written `Puder.IsPrimitiveIn ⊤ w` (a basis of the subgroup $\top$, indexed by some type, one of whose elements is $w$). Then for every subgroup $J \le \mathbf F_d$ with $w \in J$, the element $w$ is primitive in $J$ (`Puder.IsPrimitiveIn J w`): some basis of $J$ contains $w$. No finiteness of the rank of $J$ is assumed.
--
--   Puder, p. 8: “If $w$ is primitive in $\mathbf F_k$, it is also primitive in every subgroup $J \le \mathbf F_k$ (e.g. [Pud14, Claim 2.5]).” Here “every subgroup” means every subgroup containing $w$. The cited Claim 2.5(3) of Puder, *Primitive words, free factors and measure preservation*, Israel J. Math. 201 (2014) 25–73, https://doi.org/10.1007/s11856-013-0055-2 (arXiv:1104.3991, p. 13), reads “If $H \overset{*}{\le} J$ then $H$ is a free factor in any subgroup $H \le M \le J$ in between.”; the statement above is its case $H = \langle w \rangle$, $J = \mathbf F_k$, since $w$ is primitive in a free group exactly when $\langle w \rangle$ is a free factor of it. Puder's $k$ is $d$ here.
--
--   Sources: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 8); D. Puder, *Primitive words, free factors and measure preservation*, Israel J. Math. 201 (2014) 25–73, https://doi.org/10.1007/s11856-013-0055-2, Claim 2.5.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 8, §2, Step II, which cites Puder, D., Primitive words, free factors and measure preservation, Israel J. Math. 201 (2014) 25–73, https://doi.org/10.1007/s11856-013-0055-2 (arXiv:1104.3991), Claim 2.5

import Mathlib
import Definitions.Def_StrongConvPuder

namespace Puder

theorem isPrimitiveIn_of_isPrimitiveIn_top {d : ℕ} {w : FreeGroup (Fin d)} (hw : IsPrimitiveIn ⊤ w)
    (J : Subgroup (FreeGroup (Fin d))) (hJ : w ∈ J) : IsPrimitiveIn J w := by
  sorry

end Puder
