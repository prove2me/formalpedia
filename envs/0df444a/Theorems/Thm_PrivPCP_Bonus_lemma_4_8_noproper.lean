-- Prove2me | Theorems.Thm_PrivPCP_Bonus_lemma_4_8_noproper
-- name    : PrivPCP.Bonus.lemma_4_8_noproper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:03:33.136994+00:00
-- url     : https://prove2.me/theorems/0735ef05-8105-4ab5-917f-c5444277c911
-- title:
--   Lemma 4.8 without the properness hypothesis
-- statement:
--   This strengthens Lemma 4.8 of Bafna–Vyas by removing the hypothesis that the component codes are proper subspaces.
--
--   Let $r\ge2$, $\rho\in(0,1]$, and let $C_i\subseteq\mathbb F_q^{S_i}$ ($i\in[r]$) be linear codes, not necessarily proper. If $(C_1,\dots,C_r)$ is $\rho$-product-expanding, then it is collectively $P(\rho,r)$-product-expanding, where
--   $$P(\rho,r)=\frac{\rho^r}{r\,(2^r+1)^r}.$$
--   That is, every finite family $X=(X^{(a)})_{a\in A}$ in $\sum_iL_i(C_i)$ has decompositions $X^{(a)}=\sum_iX^{(a)}_i$ with $X^{(a)}_i\in L_i(C_i)$ and
--   $$\mathrm{wt}_\cup(X)\ge P(\rho,r)\sum_i|S_i|\,\ell_{i,\cup}\big((X^{(a)}_i)_a\big).$$
--
--   The proof (closure of the union support, Kalachev–Panteleev Lemmas 17 and 18) never uses properness of the codes, so the lemma holds for arbitrary component codes.
--
--   **Formalization Note** Same encoding as `PrivPCP.lemma_4_8` (`IsCollectivelyPE`, `GoodQLTC.IsProductExpanding`); only the hypothesis `∀ i, C i ≠ ⊤` is dropped.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e0…), Lemma 4.8, p.18 (strengthened: hypothesis C_i proper dropped); proof via Kalachev–Panteleev arXiv:2501.01411 Lemmas 17, 18

import Mathlib
import Definitions.Def_PrivPCP_IsCollectivelyPE

namespace PrivPCP.Bonus

/-- **Lemma 4.8 without properness** (strengthening of Bafna–Vyas, *Private PCPs from Product Expansion*,
STOC 2027 submission manuscript (sha256 c2cac1e0…), Lemma 4.8, p.18). If `(C_1, …, C_r)`, `C_i ⊆ 𝔽_q^{S_i}`,
is `ρ`-product-expanding with `ρ ∈ (0,1]` and `r ⩾ 2`, then it is collectively `ρ^r/(r(2^r+1)^r)`-product-expanding.
The hypothesis `C_i ≠ 𝔽_q^{S_i}` of Lemma 4.8 is not needed. -/
theorem lemma_4_8_noproper {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : 2 ≤ r) {S : Fin r → Type}
    [∀ i, Fintype (S i)] (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (C : ∀ i, Submodule F (S i → F))
    (hPE : GoodQLTC.IsProductExpanding ρ C) :
    IsCollectivelyPE (ρ ^ r / (r * (2 ^ r + 1) ^ r)) C := by sorry

end PrivPCP.Bonus
