-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_6
-- name    : PrivPCP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:30.665336+00:00
-- url     : https://prove2.me/theorems/addfda5b-1173-4e84-8ced-9a0b11f48980
-- title:
--   Lemma 4.6: relative dual distance from product expansion
-- statement:
--   Work in the general set-up of §4: $k\ge2$, finite sets $S_1,\dots,S_k$, $N=\prod_i|S_i|$, nested codes $0\ne K_i\subsetneq V_i\subseteq\mathbb F_q^{S_i}$, $U_i=V_i^\perp$, $W_i=K_i^\perp$, $C=\bigotimes_iV_i$ and $K=\sum_i K_i\otimes\bigotimes_{j\ne i}V_j$. Put
--   $$\delta_i=\frac{\min\{\mathrm{wt}(w):w\in W_i\setminus U_i\}}{s_i},\qquad\delta=\min_i\delta_i.$$
--   If for every $t<k$ the tuple $(W_t,U_{t+1},\dots,U_k)$ on $\prod_{i\ge t}S_i$ is $\rho$-product-expanding, then
--   $$\mathrm{wt}(M)\ge\delta\,\rho^{k-1}N\qquad(M\in K^\perp\setminus C^\perp).$$
--
--   The quantity $\min\{\mathrm{wt}(M):M\in K^\perp\setminus C^\perp\}$ is the $Z$-distance of the CSS code $(C,K)$ and the privacy threshold of the randomized encoding that samples a uniform element of a coset of $K$ in $C$; the lemma bounds it by a constant fraction of the length.
--
--   **Formalization Note** Coordinates are numbered $0,\dots,k-1$; "$t<k$" is every coordinate but the last. Product expansion is the published `GoodQLTC.IsProductExpanding`.
--
--   Differences from the source:
--   - encoding: coordinates $1,\dots,k$; $t<k$; subtuple on $\prod_{i\ge t}S_i$ → `Fin k`; $t+1<k$; the subtype $\{i\mid t\le i\}$; reason: re-indexing; same tuples
--   - encoding: $\mathbb F_q$ → any finite field; reason: the paper's $\mathbb F_q$ is a finite field; same instances
--   - encoding: $\rho$-product-expanding → `GoodQLTC.IsProductExpanding`, which includes $\rho>0$; reason: Definition 4.1 is used for positive $\rho$; at $\rho=0$ the conclusion is trivial and for $\rho<0$ the printed statement is not meant (it fails for odd $k$)
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 4.6, p.16 (PDF p.18); §4 set-up, pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_PrivPCP_NestedCodes

namespace PrivPCP

/-- **Lemma 4.6 (Relative dual distance)** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Lemma 4.6, p.16, in the set-up of §4, pp.12–13). Let `k ⩾ 2`, let
`S_1, …, S_k` be finite sets, `N = ∏_i |S_i|`, and fix nested codes `0 ≠ K_i ⊊ V_i ⊆ 𝔽_q^{S_i}` with
`U_i = V_i^⊥`, `W_i = K_i^⊥`, `C = ⊗_i V_i`, `K = ∑_i K_i ⊗ ⊗_{j≠i} V_j`. Put
`δ_i = min{wt(w) : w ∈ W_i ∖ U_i}/s_i` and `δ = min_i δ_i`. If for every `t < k` the tuple
`(W_t, U_{t+1}, …, U_k)` is `ρ`-product-expanding, then `wt(M) ⩾ δ ρ^{k−1} N` for every `M ∈ K^⊥ ∖ C^⊥`.

**Formalization Note** Coordinates are `Fin k` (`0, …, k−1`); "`t < k`" is every `t` but the last. The
subtuple `(W_t, U_{t+1}, …, U_k)` lives on `∏_{i ⩾ t} S_i`, indexed by the subtype `{i // i ∈ {i | t ≤ i}}`.
`𝔽_q` is any finite field. Product expansion is the published `GoodQLTC.IsProductExpanding` (it includes
`0 < ρ`). -/
theorem lemma_4_6 {F : Type} [Field F] [Fintype F] {k : ℕ} (hk : 2 ≤ k) {S : Fin k → Type}
    [∀ i, Fintype (S i)] (X : NestedCodes F (Fin k) S) (hX : X.Valid) (ρ : ℝ)
    (hPE : ∀ t : Fin k, t.val + 1 < k →
      GoodQLTC.IsProductExpanding ρ
        ((X.restrict (Finset.univ.filter fun i => t ≤ i)).mixed fun i => decide (i.val ≠ t))) :
    ∀ M ∈ X.Dbig, M ∉ X.B →
      (⨅ i, X.relDualDist i) * ρ ^ (k - 1) * (Fintype.card (∀ i, S i) : ℝ) ≤ GoodQLTC.supportCard M := by sorry

end PrivPCP
