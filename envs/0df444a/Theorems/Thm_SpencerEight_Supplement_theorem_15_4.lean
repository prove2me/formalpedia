-- Prove2me | Theorems.Thm_SpencerEight_Supplement_theorem_15_4
-- name    : SpencerEight.Supplement.theorem_15_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:52:58.656192+00:00
-- url     : https://prove2.me/theorems/63f4b95a-4fba-4498-89b7-153c634cabfc
-- title:
--   Theorem 15.4 — sixteen $16\times16$ words with discrepancy exactly $1+\sqrt{z^*}$, so $D^{\mathrm{mat}}_{16}/4\ge1.962541779\ldots$
-- statement:
--   Let $A_1,\dots,A_{16}\in\mathbb R^{16\times16}$ be the Kronecker words
--   $$
--   IIII,\ XZZZ,\ ZJXJ,\ JIZJ,\ JZJZ,\ ZXXX,\ JIJI,\ XZJJ,\ JJXX,\ XXXI,\ XIXZ,\ JIJZ,\ IJJX,\ JJII,\ XZXI,\ ZIIZ
--   $$
--   in the letters $I,X,Z,J$ of Section 15.2, and let $z^*$ be the largest root of $q(z):=z^4-88z^3+2226z^2-14112z+4805$. Then:
--
--   1. each $A_i$ is a real symmetric signed permutation matrix with $A_i^2=I_{16}$;
--   2. $\mathrm{disc}_{\mathrm{mat}}(A_1,\dots,A_{16})=1+\sqrt{z^*}$;
--   3. $z^*=46.9247895\ldots$ and $1+\sqrt{z^*}=7.8501671176958\ldots$;
--   4. the certified bracket holds:
--   $$
--   \frac{7850167116695}{10^{12}}<\mathrm{disc}_{\mathrm{mat}}(A_1,\dots,A_{16})<\frac{7850167118696}{10^{12}};
--   $$
--   5. consequently $D^{\mathrm{mat}}_{16}/4\ge1.962541779\ldots$.
--
--   The family is an explicit lower bound on the Matrix Spencer constant at $n=16$: no signing of these sixteen involutions has norm below $7.850\ldots=1.9625\ldots\cdot\sqrt{16}$.
--
--   **Formalization Note** "Largest root" means $q(z^*)=0$ and every real root of $q$ is at most $z^*$. Truncated decimals are stated as intervals ($46.9247895\le z^*<46.9247896$, and likewise for $1+\sqrt{z^*}$). The words are 16×16 matrices on indices in standard Kronecker order.
--
--   Differences from the source:
--   - encoding: z* is the largest root of q → q(z) = 0 ∧ every real root w of q satisfies w ≤ z; reason: definition of the largest (real) root; same number
--   - encoding: truncated decimals z* = 46.9247895…, 1 + √z* = 7.8501671176958… → 46.9247895 ≤ z < 46.9247896 and 7.8501671176958 ≤ 1 + √z < 7.8501671176959; reason: the source's convention (p.288) that a decimal followed by an ellipsis is a truncated expansion
--   - reading: D^mat_16/4 ≥ 1.962541779… → (1 + √z)/4 ≤ D^mat_16/4 ∧ 1.962541779 ≤ (1 + √z)/4 < 1.962541780; reason: the truncated decimal stands for the number (1 + √z*)/4 given by the family; this reading implies D^mat_16/4 ≥ 1.962541779
--   - encoding: A_1, …, A_16 ∈ ℝ^{16×16} → family16 : Fin 16 → Matrix (Fin (2^4)) (Fin (2^4)) ℝ, family16 i = A_{i+1}; reason: 0-based indexing and the standard Kronecker index order; same matrices
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 15.4, p.290 (PDF p.290); letters and words p.289; Definition 15.1 pp.288-289

import Mathlib
import Definitions.Def_SpencerEight_Supplement_IsSignedPerm
import Definitions.Def_SpencerEight_Supplement_family16
import Definitions.Def_SpencerEight_Supplement_discmat
import Definitions.Def_SpencerEight_Supplement_Dmat

namespace SpencerEight.Supplement

/-- Theorem 15.4 (A family at `n = 16` with discrepancy exactly `1 + √z*`), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.290
(PDF p.290). For the sixteen words `A₁, …, A₁₆` of `family16`:

1. each `Aᵢ` is a real symmetric signed permutation matrix with `Aᵢ² = I₁₆`;
2. `discmat(A₁, …, A₁₆) = 1 + √z*`, where `z*` is the largest root of
   `q(z) = z⁴ − 88z³ + 2226z² − 14112z + 4805`;
3. `z* = 46.9247895…` and `1 + √z* = 7.8501671176958…` (truncated decimals);
4. `7850167116695/10¹² < discmat(A₁, …, A₁₆) < 7850167118696/10¹²`;
5. `D^mat_16 / 4 ≥ 1.962541779…`.

**Formalization Note** "Largest root" is: `q z* = 0` and every real root of `q` is at most `z*`. A decimal
followed by an ellipsis is a truncated expansion, so `z* = 46.9247895…` is
`46.9247895 ≤ z* < 46.9247896`, and likewise for `1 + √z*`. Clause 5 is read as
`D^mat_16/4 ≥ (1 + √z*)/4` together with the truncation `1.962541779 ≤ (1 + √z*)/4 < 1.962541780`;
`4 = √16`. -/
theorem theorem_15_4 :
    (∀ i, (family16 i).IsSymm ∧ IsSignedPerm (family16 i) ∧ family16 i * family16 i = 1) ∧
    ∃ z : ℝ, z ^ 4 - 88 * z ^ 3 + 2226 * z ^ 2 - 14112 * z + 4805 = 0 ∧
      (∀ w : ℝ, w ^ 4 - 88 * w ^ 3 + 2226 * w ^ 2 - 14112 * w + 4805 = 0 → w ≤ z) ∧
      discmat family16 = 1 + Real.sqrt z ∧
      46.9247895 ≤ z ∧ z < 46.9247896 ∧
      7.8501671176958 ≤ 1 + Real.sqrt z ∧ 1 + Real.sqrt z < 7.8501671176959 ∧
      (7850167116695 : ℝ) / 10 ^ 12 < discmat family16 ∧
      discmat family16 < (7850167118696 : ℝ) / 10 ^ 12 ∧
      (1 + Real.sqrt z) / 4 ≤ Dmat 16 / 4 ∧
      1.962541779 ≤ (1 + Real.sqrt z) / 4 ∧ (1 + Real.sqrt z) / 4 < 1.962541780 := by sorry

end SpencerEight.Supplement
