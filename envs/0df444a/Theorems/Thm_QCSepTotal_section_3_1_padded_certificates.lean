-- Prove2me | Theorems.Thm_QCSepTotal_section_3_1_padded_certificates
-- name    : QCSepTotal.section_3_1_padded_certificates
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:58.387831+00:00
-- url     : https://prove2.me/theorems/ce1ffdf8-1849-4bb8-8653-7cffc2935cca
-- title:
--   Section 3.1 — padded certificates: valid and invalid $b$-bit certificates exist iff $D_c(x,y)=1$
-- statement:
--   Let $D$ be a predicate on a set $Z$, let $1\le b_0\le b$, and let $V_0(z;p)$ be a predicate on certificates $p\in\mathbb F_2^{b_0}$ such that exactly one certificate is valid when $D(z)=1$ and none is valid when $D(z)=0$. Let $V(z;p)$, for $p\in\mathbb F_2^b$, apply $V_0$ to the first $b_0$ bits of $p$ and ignore the rest. Then for every $z$:
--
--   1. if $D(z)=1$, there exist both a valid and an invalid $b$-bit certificate for $z$;
--   2. if $D(z)=0$, no $b$-bit certificate is valid for $z$.
--
--   In Section 3.1 this is applied with $D=D_c$ on pairs of $c$-tuples. It is what makes $g(p)=V(x,y;p)$ take both values in Claim 1, and what makes $F_{\mathrm{tot}}$ vanish off $D_c$ in Theorem 3.2.
--
--   Differences from the source:
--   - generalization: D_c and the predicate V₀ of Proposition 2.4 for its circuit → any predicate D on any type Z and any V₀ with properties 1 and 2 of Proposition 2.4; reason: the proof uses only these properties; D = D_c is a special case
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §3.1, p.6

import Mathlib
import Definitions.Def_QCSepTotal_Ftot

namespace QCSepTotal

/-- **Section 3.1, padded certificates** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.6). Define `V(x, y; p)` on
`b`-bit certificates by applying the original predicate to the first `b₀` bits and ignoring the
remaining bits. Since `b₀ ≥ 1` and the original certificate is unique, if `D_c(x, y) = 1` then
there exist both valid and invalid `b`-bit certificates; if `D_c(x, y) = 0`, none is valid.

**Formalization Note.** Stated for any predicate `D` on any input type `Z` (the paper's `D_c`
on pairs of tuples) and any `V₀` with properties 1 and 2 of Proposition 2.4. -/
theorem section_3_1_padded_certificates {Z : Type} (D : Z → Bool) {b₀ b : ℕ} (hb₀ : 1 ≤ b₀)
    (h : b₀ ≤ b) (V₀ : Z → (Fin b₀ → ZMod 2) → Bool)
    (h1 : ∀ z, D z = true → ∃! p, V₀ z p = true) (h2 : ∀ z, D z = false → ∀ p, V₀ z p = false)
    (z : Z) :
    (D z = true → (∃ p, padCert h V₀ z p = true) ∧ (∃ p, padCert h V₀ z p = false)) ∧
      (D z = false → ∀ p, padCert h V₀ z p = false) := by sorry

end QCSepTotal
