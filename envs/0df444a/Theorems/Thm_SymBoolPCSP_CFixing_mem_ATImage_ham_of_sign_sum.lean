-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_mem_ATImage_ham_of_sign_sum
-- name    : SymBoolPCSP.CFixing.mem_ATImage_ham_of_sign_sum
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:08:57.805974+00:00
-- url     : https://prove2.me/theorems/5a6df09a-2c9e-4663-8ff7-7e1f58c5774f
-- title:
--   AT(Ham_k(S)) contains every positivity pattern whose total is ≡ ℓ (mod ℓ′ − ℓ)
-- statement:
--   Let $k \ge 0$, $S \subseteq \mathbb Z_{\ge 0}$, and suppose $\ell, \ell' \in S$ with $1 \le \ell \le k-1$ and $\ell' \le k$. Let $y \in \{0,1\}^k$ have Hamming weight $|y|$, and let $T \in \mathbb Z$ satisfy
--
--   $$
--   (\ell' - \ell) \mid T - \ell
--   $$
--
--   and
--
--   $$
--   \big(y \ne 0^k \text{ and } |y| \le T\big) \quad\text{or}\quad \big(y \ne 1^k \text{ and } T \le |y|\big).
--   $$
--
--   Then $y \in \mathrm{AT}(\mathrm{Ham}_k(S))$, where $\mathrm{AT}(P) = \bigcup_{L\text{ odd}} \mathrm{AT}_L(P)$ with $\mathrm{AT}_L$ the alternating-threshold function.
--
--   The second condition says exactly that some integer vector $t \in \mathbb Z^k$ with total $\sum_c t_c = T$ has positivity pattern $y$. The first says that $T$ is a possible total of a vector in the affine lattice spanned by $\mathrm{Ham}_k(S)$.
--
--   This gives the inclusions "$\supseteq$" in parts 4 and 5 of Claim 4.6 of Brakensiek–Guruswami: take $\ell' = \ell$ and $T = \ell$ for $S = \{\ell\}$, or $T = \ell \pm (\ell'-\ell)^2 k$ for a two-element $S$. The bound $\ell \le k-1$ is used to move single units between coordinates while keeping the row weight $\ell$.
--
--   **Formalization Note** The disjunction is stated with `∃ c, y c = true` / `∃ c, y c = false` and casts of `hw y` to `ℤ`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.2, Claim 4.6 (parts 4–5) and its proof, p. 17

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- `AT(Ham_k(S))` contains every `y ∈ {0,1}^k` that is the positivity pattern of an integer vector with total `T`, whenever `T ≡ ℓ (mod ℓ' - ℓ)` for some `ℓ, ℓ' ∈ S` with `1 ≤ ℓ ≤ k - 1`, `ℓ' ≤ k`; the condition on `(y, T)` is exactly that such an integer vector exists. -/
theorem mem_ATImage_ham_of_sign_sum {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (y : Fin k → Bool) (T : ℤ)
    (hT : ((l' : ℤ) - l) ∣ T - l)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    y ∈ ATImage (Ham k S) := by sorry

end SymBoolPCSP.CFixing
