-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_proposition_4_4
-- name    : SmallSecretLWE.Classical.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:57.063201+00:00
-- url     : https://prove2.me/theorems/53c99cd0-c39b-4e8f-bcff-114a121d332e
-- title:
--   Proposition 4.4 — $L$ i.i.d. draws contain an $R$-close pair with probability $\ge1-\prod_j(1-j/|S|)\ge1-e^{-L(L-1)/(2|S|)}$
-- statement:
--   Let $\mathcal D$ be a distribution on the vertices $(\mathbb Z_q^n)_l$ of $K_l(A)$, $R\ge0$, and let $S\subseteq\mathrm{Supp}(\mathcal D)$ be a maximal set of $R/2$-faraway points. Then
--   $$\Pr_{w_1,\dots,w_L\overset{iid}{\sim}\mathcal D}\big[\exists\,i\ne i':\ \|w_i-w_{i'}\|_1\le R\big]\ \ge\ 1-\prod_{j=1}^{L-1}\Big(1-\frac{j}{|S|}\Big)\ \ge\ 1-\exp\Big(-\frac{L(L-1)}{2|S|}\Big).$$
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: '$S\subseteq\mathrm{Supp}(\mathcal D)$ a maximal set of $R/2$-faraway points' → $S$ is $R/2$-faraway, $S\subseteq\mathrm{Supp}(\mathcal D)$, and every $v\in\mathrm{Supp}(\mathcal D)\setminus S$ is within $R/2$ of $S$; reason: the proof uses maximality only inside the support; maximality in all of $(\mathbb Z_q^n)_l$ implies it, so this is the stronger reading
--   - reading: '$R$-faraway: $\|u-v\|_1>R$ for all $u,v\in S$' → for all distinct $u,v\in S$; reason: the literal reading allows only $S=\emptyset$ since $\|u-u\|_1=0$
--   - reading: $R$ (range not stated) → hypothesis $0\le R$; reason: $R$ is the relaxation parameter $R\ge0$ of Definition 2.2, standing throughout §4
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 20, Proposition 4.4

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

open scoped Classical

namespace SmallSecretLWE.Classical

/-- Proposition 4.4. Let `D` be a law on `(Z_q^n)_l`, `R ≥ 0`, and `S ⊆ Supp(D)` a maximal
`R/2`-faraway subset of `Supp(D)`. For `L` i.i.d. draws `w_1, …, w_L ∼ D`,
`Pr[∃ i ≠ i', ‖w_i − w_{i'}‖_1 ≤ R] ≥ 1 − Π_{j=1}^{L−1} (1 − j/|S|) ≥ 1 − exp(−L(L−1)/(2|S|))`. -/
theorem proposition_4_4 {n q l : ℕ} [NeZero q] (D : PMF (KVert n q l)) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset (KVert n q l)) (hS : IsMaxFarawayIn (R / 2) S (Finset.univ.filter fun v => D v ≠ 0))
    (L : ℕ) :
    1 - ∏ j ∈ Finset.Icc 1 (L - 1), (1 - (j : ℝ) / S.card) ≤
      (∑ w : Fin L → KVert n q l,
        if ∃ i i', i ≠ i' ∧ l1 ((w i).val - (w i').val) ≤ R then ∏ i, (D (w i)).toReal else 0) ∧
    1 - Real.exp (-((L : ℝ) * ((L : ℝ) - 1)) / (2 * S.card)) ≤
      1 - ∏ j ∈ Finset.Icc 1 (L - 1), (1 - (j : ℝ) / S.card) := by sorry

end SmallSecretLWE.Classical
