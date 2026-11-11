-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_8_9
-- name    : QuadExt.Main.theorem_8_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:04:39.451923+00:00
-- url     : https://prove2.me/theorems/d28c6100-5b6b-4c9a-8cd7-f17383abc305
-- title:
--   Theorem 8.9 — field size reduction: $W(i,s) = L_s M(U_i)$ is a $(dh, r/(hm), \varepsilon+\delta)$-rank combiner over $\mathbb F_2$
-- statement:
--   Let $U_1, \dots, U_N \in \mathbb F_{2^h}^{m \times n}$ be a $(d, r, \varepsilon)$-rank combiner over $\mathbb F_{2^h}$ and let $\mathrm{LExt} : \mathbb F_2^{hm} \times \{0,1\}^\ell \to \mathbb F_2^{m'}$ be an $(m, \delta)$-strong linear seeded extractor. Fix a basis $e_1, \dots, e_h$ of $\mathbb F_{2^h}$ over $\mathbb F_2$, write $U = \sum_j M_j(U) e_j$ with $M_j(U) \in \mathbb F_2^{m \times n}$, stack $M(U) = (M_1(U); \dots; M_h(U))$, and let $L_s$ be the matrix of $\mathrm{LExt}(\cdot, s)$. Then the $N \cdot 2^\ell$ matrices
--   $$W(i, s) = L_s\, M(U_i) \in \mathbb F_2^{m' \times n}, \qquad i \in [N],\ s \in \{0,1\}^\ell,$$
--   form a $(dh, r/(hm), \varepsilon + \delta)$-rank combiner over $\mathbb F_2$. This transfers the large-field construction of Theorem 8.5 to $\mathbb F_2$ at the cost of the factor $hm$ in the rank.
--
--   Differences from the source:
--   - generalization: explicit $U$ and explicit LExt → any rank combiner $U$ and any $(m, \delta)$-strong linear seeded extractor, and "there is an explicit … rank combiner" → the construction $W(i, s) = L_s M(U_i)$ of the proof, for every basis; reason: the explicit objects are instances and the construction is explicit when they are, so this specializes to the paper's.
--   - encoding: $h \ge 1$ and $m \ge 1$ assumed; reason: $\mathbb F_{2^h}$ (`GaloisField 2 h`) is meant as a field with $2^h$ elements, and $r/(hm)$ is undefined at $hm = 0$.
--   - encoding: stacking order of $M(U)$ (block $j$, row $\rho$ at position $\rho + mj$) and seeds $\{0,1\}^\ell$ as `Fin ℓ → ZMod 2`; reason: Lean index conventions; LExt is arbitrary, so the order is immaterial.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 29 (PDF 30), Theorem 8.9 and its proof

import Mathlib
import Definitions.Def_QuadExt_Main_SeededExt
import Definitions.Def_QuadExt_Main_RankCombiner

namespace QuadExt.Main

/-- **Theorem 8.9** (field size reduction, p. 29), "explicit" read as the construction of its
proof: if `U_1, …, U_N ∈ 𝔽_{2^h}^{m×n}` is a `(d, r, ε)`-rank combiner over `𝔽_{2^h}` and
`LExt : 𝔽₂^{hm} × {0,1}^ℓ → 𝔽₂^{m′}` is an `(m, δ)`-strong linear seeded extractor, then for every
basis `e` of `𝔽_{2^h}` over `𝔽₂` the matrices `W(i, s) = L_s M(U_i)` (`i ∈ [N]`, `s ∈ {0,1}^ℓ`,
`M = N·2^ℓ` of them) form a `(dh, r/(hm), ε + δ)`-rank combiner in `𝔽₂^{m′×n}`. -/
theorem theorem_8_9 (h m n N ℓ m' d : ℕ) (hh : 0 < h) (hm : 0 < m) (r ε δ : ℝ)
    (U : Fin N → Matrix (Fin m) (Fin n) (GaloisField 2 h)) (hU : IsRankCombiner d r ε U)
    (LExt : (Fin (h * m) → ZMod 2) → (Fin ℓ → ZMod 2) → (Fin m' → ZMod 2))
    (hLExt : IsSLSE m δ δ LExt)
    (e : Module.Basis (Fin h) (ZMod 2) (GaloisField 2 h)) :
    IsRankCombiner (d * h) (r / (h * m)) (ε + δ) (fieldReduce e LExt U) := by sorry

end QuadExt.Main
