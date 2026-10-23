-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_lemma_2
-- name    : PrivacyParadox.Alloc.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:23.184235+00:00
-- url     : https://prove2.me/theorems/35e0caac-9c62-4f25-aca9-08d3bdcda894
-- title:
--   Lemma 2, p. 23 — the adversary's best responses p are characterized by the sign of the bracket G_k(A, p)
-- statement:
--   In the discrete program (39), fix an allocation $A$ with $A_k>0$ for $k=1,\dots,K$, and an admissible $p$ ($0\le p_k\le1$). Write
--   $$G_k(A,p)=\frac{\gamma}{s(\bar\theta^*)^2}\Big(\frac{1}{A_k}-\frac{2}{\bar\theta^*}\sum_{j=1}^K\pi_jp_j\Big)-\frac{1}{\bar\theta^*}(1-\bar\theta^*)(1-\gamma).$$
--   Then $p$ maximizes $U(A,\cdot)$ over admissible choices if and only if, for every $k$, one of the following holds:
--
--   1. $p_k=1$ and $G_k(A,p)>0$;
--   2. $p_k=0$ and $G_k(A,p)<0$;
--   3. $0\le p_k\le1$ and $G_k(A,p)=0$.
--
--   This is the maximizing player's half of the saddle-point analysis of (39).
--
--   **Formalization Note** The paper's double index $ij$ is replaced by the sorted index $k$ of p. 25. The bracket omits the factor $\pi_k$ of $\partial U/\partial p_k$, which is harmless because $\pi_k>0$.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 23, Lemma 2 (proof p. 24, (42)–(44))

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem lemma_2 (P : Prog) (hP : P.Standing) (A : ℕ → ℝ)
    (hA : ∀ k ∈ Finset.Icc 1 P.K, 0 < A k) (p : ℕ → ℝ) (hp : P.AdmP p) :
    (∀ p' : ℕ → ℝ, P.AdmP p' → P.U A p' ≤ P.U A p) ↔
      ∀ k ∈ Finset.Icc 1 P.K,
        (p k = 1 ∧ 0 < P.Gk A p k) ∨ (p k = 0 ∧ P.Gk A p k < 0) ∨
          (0 ≤ p k ∧ p k ≤ 1 ∧ P.Gk A p k = 0) := by sorry

end PrivacyParadox.Alloc
