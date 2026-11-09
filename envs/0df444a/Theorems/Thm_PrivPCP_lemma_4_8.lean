-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_8
-- name    : PrivPCP.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:44:43.075959+00:00
-- url     : https://prove2.me/theorems/c718a6e7-1ada-4cf1-a02b-f7ab65530ed5
-- title:
--   Lemma 4.8: collective product expansion from product expansion
-- statement:
--   Let $r\ge2$, $\rho\in(0,1]$, and let $C_i\subsetneq\mathbb F_q^{S_i}$, $i\in[r]$, be proper linear codes on finite sets $S_i$. If $(C_1,\dots,C_r)$ is $\rho$-product-expanding, then it is collectively $P(\rho,r)$-product-expanding, where
--   $$P(\rho,r)=\frac{\rho^r}{r(2^r+1)^r}.$$
--
--   Collective product expansion lets the robust-testability induction of Lemma 4.9 handle vector-valued words; the explicit $P(\rho,r)$ is what makes the constant of Corollary 4.10 $\exp(O(k^3+k^2\log(1/\rho)))$.
--
--   **Formalization Note** The finite families range over index types in the lowest universe.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ → any finite field; reason: same instances
--   - encoding: finite families $(X^{(a)})_{a\in A}$ → families indexed by finite types `A : Type`; reason: every finite index set is in bijection with such a type
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 4.8, p.18 (PDF p.20); Definition 4.7, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PrivPCP_IsCollectivelyPE

namespace PrivPCP

/-- **Lemma 4.8 (Collective PE from PE)** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Lemma 4.8, p.18, with Definition 4.7, p.18). Let `r ⩾ 2`,
`ρ ∈ (0,1]`, and let `C_i ⊊ 𝔽_q^{S_i}`, `i ∈ [r]`, be proper linear codes. If `(C_1, …, C_r)` is
`ρ`-product-expanding, then it is collectively `P(ρ, r)`-product-expanding, where
`P(ρ, r) = ρ^r / (r(2^r + 1)^r)`.

**Formalization Note** `𝔽_q` is any finite field and the `S_i` are any finite sets; collective product expansion
quantifies over finite families indexed by types in `Type`. -/
theorem lemma_4_8 {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : 2 ≤ r) {S : Fin r → Type}
    [∀ i, Fintype (S i)] (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (C : ∀ i, Submodule F (S i → F)) (hC : ∀ i, C i ≠ ⊤)
    (hPE : GoodQLTC.IsProductExpanding ρ C) :
    IsCollectivelyPE (ρ ^ r / (r * (2 ^ r + 1) ^ r)) C := by sorry

end PrivPCP
