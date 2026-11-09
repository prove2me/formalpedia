-- Prove2me | Theorems.Thm_PrivPCP_fact_3_3
-- name    : PrivPCP.fact_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:44:04.601583+00:00
-- url     : https://prove2.me/theorems/997974bf-7b09-48e5-b75a-c16c037d6b17
-- title:
--   Fact 3.3: vanishing on a Cartesian grid
-- statement:
--   Let $H_1,\dots,H_k\subseteq\mathbb F_q$ be finite sets, put $D=\prod_{i=1}^k H_i$, $Z_i(X_i)=\prod_{c\in H_i}(X_i-c)$ and $h_i=|H_i|$. Let $a=(a_1,\dots,a_k)$ be a degree profile with $a_i\ge h_i$ for every $i$, and
--   $$Q_i(a)=\{Q:\ \deg_{X_i}Q\le a_i-h_i,\ \deg_{X_j}Q\le a_j\ (j\ne i)\}.$$
--   A polynomial $R\in\mathbb F_q[X_1,\dots,X_k]$ with $\deg_{X_i}R\le a_i$ for every $i$ vanishes on $D$ if and only if
--   $$R=\sum_{i=1}^k Z_i\,Q_i\qquad\text{with each }Q_i\in Q_i(a).$$
--
--   This is Alon's description of the polynomials vanishing on a grid, with degree control. It gives the identities (4) of §4.1 and the surjectivity of the certificate map $\Phi_a$ of (23).
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ → any finite field; reason: the paper's $\mathbb F_q$ is a finite field; same instances
--   - reading: a polynomial with degree profile $a$ → $\deg_{X_i}R\le a_i$ for every $i$; reason: the paper's $P_a$ (p.30) is individual degree at most $a$
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Fact 3.3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_PrivPCP_gridQ

namespace PrivPCP

/-- **Fact 3.3 (Vanishing on a Cartesian grid [Alo99])** (Bafna, Vyas, *Private PCPs from Product Expansion*,
STOC 2027 submission manuscript (sha256 c2cac1e0…), Fact 3.3, p.12). Let `H_1, …, H_k ⊆ 𝔽_q` be finite sets,
`D = ∏_i H_i`, `Z_i(X_i) = ∏_{c∈H_i}(X_i − c)`, `h_i = |H_i|`, and let `a` be a degree profile with `a_i ⩾ h_i`.
A polynomial `R` with `deg_{X_i} R ⩽ a_i` for every `i` vanishes on `D` if and only if `R = ∑_i Z_i Q_i` with
each `Q_i ∈ Q_i(a)`.

**Formalization Note** `𝔽_q` is any finite field. "With degree profile `a`" is read as `deg_{X_i} R ⩽ a_i` for
every `i` (`MvPolynomial.degreeOf`). -/
theorem fact_3_3 {F : Type} [Field F] [Fintype F] {k : ℕ} (H : Fin k → Finset F) (a : Fin k → ℕ)
    (ha : ∀ i, (H i).card ≤ a i) (R : MvPolynomial (Fin k) F) (hR : ∀ i, R.degreeOf i ≤ a i) :
    (∀ x : Fin k → F, (∀ i, x i ∈ H i) → MvPolynomial.eval x R = 0) ↔
      ∃ Q : Fin k → MvPolynomial (Fin k) F, (∀ i, Q i ∈ gridQ H a i) ∧ R = ∑ i, gridZ H i * Q i := by sorry

end PrivPCP
