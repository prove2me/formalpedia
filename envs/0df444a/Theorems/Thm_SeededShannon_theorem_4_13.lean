-- Prove2me | Theorems.Thm_SeededShannon_theorem_4_13
-- name    : SeededShannon.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T05:23:17.375984+00:00
-- url     : https://prove2.me/theorems/34fefd2e-17b8-449f-8d28-d3db85e29f45
-- title:
--   Theorem 4.13 — strongly robust PRCs and puncturable PRFs give puncturable pseudorandom codes
-- statement:
--   Fix constants $p,\varepsilon>0$ with $p+\varepsilon<\tfrac12$, a polynomially bounded input length $\ell_{in}(\lambda)\ge1$ and a polynomially bounded puncturing bound $t(\lambda)$. Suppose there are
--
--   1. a zero-bit public-key pseudorandom code $\Pi_{\mathrm{PRC}}$ (Definition 3.5: efficient and pseudorandom) with strong $(p+\varepsilon)$-robustness, negligible soundness error and codeword length $\ell_{\mathrm{prc}}=\mathrm{poly}(\lambda)$, and
--   2. a PRF $\Pi_{\mathrm{PPRF}}$ with selective puncturing at sets of at most $t$ points (Definition 3.4).
--
--   Then there is a $t$-puncturable, $p$-robust pseudorandom code (Definition 4.1) with input length $\ell_{in}$, output length $\ell_{out}=\mathrm{poly}(\ell_{in},\lambda)$, polynomial-size keys and recovery lists, and polynomial-time algorithms.
--
--   Construction 6.1 applies this theorem at radius $\tau$ and gap $r-\tau$, with $\ell_{in}=\ell_{hash}$.
--
--   **Formalization Note** Polynomial keys and recovery lists follow from the polynomial running times required in `PPRC.IsPPRCAt`.
--
--   Differences from the source:
--   - reading: a PPRC satisfying Definition 4.1 with input length ℓin → the clauses of Definition 4.1 at the input length ℓin(λ); reason: the theorem fixes ℓin before the conclusion
--   - reading: a PRC satisfying Definition 3.5 → IsEfficient ∧ Pseudorandom of the PRC; reason: Definition 3.5 is the efficient syntax plus the pseudorandomness property; robustness and soundness are listed separately
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
--   - encoding: functionality preservation with probability 1 over KeyGen and Puncture → for all coin strings; reason: the coins are finitely many and uniform, so probability 1 is every outcome
--   - encoding: a puncturing set S of size at most t → a strictly lexicographically increasing list of at most t strings of length ℓin; reason: Def. 3.4 lists S in lexicographic order; the list is the canonical representation of the set
--   - encoding: δ(Eval(K, x), y) ≤ p → Δ(Eval(K, x), y) ≤ p · ℓout; reason: same condition
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 4.13, p.29 (PDF p.32)

import Mathlib
import Definitions.Def_SeededShannon_ZeroBitPRC
import Definitions.Def_SeededShannon_PPRF
import Definitions.Def_SeededShannon_PPRC

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

/-- **Theorem 4.13 (Instantiation)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), Theorem 4.13, p.29): fix constants `p, ε > 0` with `p + ε < 1/2`, a positive
polynomially bounded input length `ℓin(λ)` and a polynomially bounded puncturing bound `t(λ)`. If
there are a zero-bit public-key PRC (Definition 3.5) with strong `(p + ε)`-robustness, negligible
soundness error and codeword length `poly(λ)`, and a PRF with selective puncturing at sets of at most
`t` points (Definition 3.4), then there is a `t`-puncturable, `p`-robust pseudorandom code
(Definition 4.1) with input length `ℓin`, output length `poly(ℓin, λ)`, polynomial-size keys and
recovery lists, and polynomial-time algorithms.

**Formalization Note** "Satisfying Definition 3.5" is efficiency and pseudorandomness of the PRC.
Output length, keys, recovery lists and running times are bounded inside `PPRC.IsPPRCAt`
(polynomial keys and lists follow from polynomial running time). -/
theorem theorem_4_13 (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hpε : p + ε < 1 / 2)
    (lin t : ℕ → ℕ) (hlin : PolyBounded lin) (hlin1 : ∀ lam, 1 ≤ lin lam) (ht : PolyBounded t)
    (hPRC : ∃ P : ZeroBitPRC, P.IsEfficient ∧ P.Pseudorandom ∧ P.StronglyRobust (p + ε) ∧
      P.NegligiblySound ∧ PolyBounded P.n)
    (hPPRF : ∃ F : PPRF, F.IsPPRF t) :
    ∃ C : PPRC, C.IsPPRCAt t p lin := by sorry

end SeededShannon
