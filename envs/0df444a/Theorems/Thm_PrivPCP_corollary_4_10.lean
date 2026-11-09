-- Prove2me | Theorems.Thm_PrivPCP_corollary_4_10
-- name    : PrivPCP.corollary_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:33.933712+00:00
-- url     : https://prove2.me/theorems/f2df7d04-ec1e-4dbc-b667-712690a48816
-- title:
--   Corollary 4.10: relative robust testability from product expansion
-- statement:
--   There is an absolute constant $C_0>0$ such that the following holds. In the general set-up of §4 ($k\ge2$, nested codes $0\ne K_i\subsetneq V_i\subseteq\mathbb F_q^{S_i}$, $D_i=E_i^\perp$, $D=\bigcap_iD_i$), let $\rho\in(0,1]$ and suppose every mixed subtuple $(C_i)_{i\in I}$ with $C_i\in\{U_i,W_i\}$ and $|I|\ge2$ is $\rho$-product-expanding. Then every $M\in\mathbb F_q^\Omega$ satisfies
--   $$\mathrm{dist}(M,D)\le C(\rho,k)\sum_{i=1}^k\mathrm{dist}(M,D_i),\qquad C(\rho,k)=\exp\!\big(C_0(k^3+k^2\log(1/\rho))\big).$$
--
--   A word that is close to each of the axis-wise spaces $D_i$ is close to their intersection; this is what converts a view of the certificate into a view of the masked polynomial in Lemma 6.2.
--
--   **Formalization Note** Distances are unnormalized.
--
--   Differences from the source:
--   - reading: $C(\rho,k)=\exp(O(k^3+k^2\log(1/\rho)))$ → $\exp(C_0(k^3+k^2\log(1/\rho)))$ with one absolute $C_0$ fixed before $k$, $\rho$, the field and the codes; reason: the standard meaning of $O(\cdot)$; the proof gives $k!\,P(\rho,k)^{-(k-1)}$ (p.22), of this form
--   - encoding: mixed subtuples $(C_i)_{i\in I}$ → a choice $b:[k]\to\{U,W\}$ restricted to $I$; reason: every mixed subtuple arises this way
--   - encoding: $\mathbb F_q$ → any finite field; reason: same instances
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Corollary 4.10, p.22 (PDF p.24); §4 set-up, pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_PrivPCP_NestedCodes

namespace PrivPCP

/-- **Corollary 4.10 (Relative robust testability)** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC
2027 submission manuscript (sha256 c2cac1e0…), Corollary 4.10, p.22, in the set-up of §4, pp.12–13). There is an
absolute constant `C₀` such that: for `k ⩾ 2`, nested codes `0 ≠ K_i ⊊ V_i ⊆ 𝔽_q^{S_i}` as in §4 and
`ρ ∈ (0,1]`, if every mixed subtuple `(C_i)_{i∈I}`, `C_i ∈ {U_i, W_i}`, `|I| ⩾ 2`, is `ρ`-product-expanding,
then every `M ∈ 𝔽_q^Ω` satisfies `dist(M, D) ⩽ C(ρ, k) ∑_i dist(M, D_i)` with
`C(ρ, k) = exp(C₀(k³ + k² log(1/ρ)))`.

**Formalization Note** "`C(ρ, k) = exp(O(k³ + k² log(1/ρ)))`" is read with one absolute `C₀`, fixed before
`k`, `ρ`, the field and the codes. A mixed subtuple on `I` is given by a choice `b : Fin k → Bool`
(`U_i` where `b i`, else `W_i`) restricted to `I`. `D = ⋂_i D_i = K^⊥`; distances are unnormalized. -/
theorem corollary_4_10 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (F : Type) [Field F] [Fintype F] (k : ℕ), 2 ≤ k →
    ∀ (S : Fin k → Type) [∀ i, Fintype (S i)] (X : NestedCodes F (Fin k) S), X.Valid →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (∀ I : Finset (Fin k), 2 ≤ I.card → ∀ b : Fin k → Bool,
        GoodQLTC.IsProductExpanding ρ ((X.restrict I).mixed fun i => b i.val)) →
      ∀ M : (∀ i, S i) → F,
        (distTo M X.Dbig : ℝ) ≤ Real.exp (C₀ * (k ^ 3 + k ^ 2 * Real.log (1 / ρ))) * ∑ i, (distTo M (X.D i) : ℝ) := by sorry

end PrivPCP
