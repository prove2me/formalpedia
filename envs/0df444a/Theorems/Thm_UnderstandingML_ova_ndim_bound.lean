-- Prove2me | Theorems.Thm_UnderstandingML_ova_ndim_bound
-- name    : UnderstandingML.ova_ndim_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:57:43.587507+00:00
-- url     : https://prove2.me/theorems/21e83665-78b2-4ebd-981f-f83113977edb
-- title:
--   Lemma 29.5: if VCdim(H_bin) = d then every set shattered by the One-versus-All class H^{OvA,k}_bin has size ≤ 3kd log(kd)
-- statement:
--   **Lemma 29.5.** If $d = \operatorname{VCdim}(H_{bin})$ then $\operatorname{Ndim}(H^{OvA,k}_{bin}) \le 3kd\log(kd)$.
--
--   Formally: every set shattered by $H^{OvA,k}_{bin}$ has size at most $3kd\log(kd)$ (natural logarithm; the bound is $0$ when $kd \le 1$). The book's step $|(H_{bin})_C| \le |C|^d$ fails for small $|C|$ (for $|C| = 2$, $d = 1$), but the statement is true: the exact Sauer count $2^c \le (\sum_{i \le d}\binom{c}{i})^k$ gives it for every $(k, d)$ except $(2, 1)$ and $(3, 1)$. In those two cases, group a shattered set by the label pair $\{f_0(x), f_1(x)\}$. On pairs $\{0, b\}$ the realized sets are $h_b \setminus h_0$, and on pairs $\{a, b\}$ with $a \ge 1$ they are $h_a$ itself. The class $\{B \setminus A : A, B \in H_{bin}\}$ cannot shatter $5$ points: on them $|H_{bin}| \le 6$, and the $6$ pairs $A = B$ all give $\emptyset$, so at most $31 < 32$ sets. Hence $|C| \le 4 < 4.16$ for $k = 2$ and $|C| \le 4 + 4 + 1 = 9 < 9.89$ for $k = 3$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.3.1 pp. 404-405, Lemma 29.5 with its proof

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 29.5** (p. 404). If `d = VCdim(H_bin)` then `Ndim(H^{OvA,k}_bin) ≤ 3kd log(kd)`, stated
for every shattered set. The book's proof uses `|(H_bin)_C| ≤ |C|^d`, which fails for small `|C|`
(`|C| = 2`, `d = 1`). The statement is nevertheless true: the exact Sauer count
`2^c ≤ (∑_{i ≤ d} (c choose i))^k` gives it except at `(k, d) = (2, 1), (3, 1)`. There, grouping a
shattered set by the label pair `{f₀(x), f₁(x)}` bounds it by `4` and by `4 + 4 + 1 = 9`,
because `{B \ A : A, B ∈ H_bin}` has at most `31` traces on `5` points. -/
theorem ova_ndim_bound {X : Type*} (Hbin : Set (X → Bool)) (d : ℕ) (hd : vcDim Hbin = d)
    (k : ℕ) [NeZero k] (C : Finset X) (hC : NShatters (ovaClass Hbin k) C) :
    (C.card : ℝ) ≤ 3 * k * d * Real.log (k * d) := by sorry

end UnderstandingML
