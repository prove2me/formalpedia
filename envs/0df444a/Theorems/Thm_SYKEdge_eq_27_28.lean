-- Prove2me | Theorems.Thm_SYKEdge_eq_27_28
-- name    : SYKEdge.eq_27_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:34.972655+00:00
-- url     : https://prove2.me/theorems/1a2d3ab2-7dde-4574-b34c-5ba2b85b68e7
-- title:
--   Eqs. (27)–(28) — spectrum $\{\lambda_j^{(d_j)}\}$ of the dense sign matrix; $q=\lambda_0$, $\delta=0$, $\rho^+=\max_{j\ge1}\lambda_j$, $\rho^-=|\lambda_1|$
-- statement:
--   Let $n\ge k\ge2$ be even with $\alpha=k^2/n<1/16$, and let $\mathcal E$ be the sign matrix of the dense hypergraph $\binom{[n]}k$. Then:
--
--   1. $\mathcal E=\binom nk^{-1}\sum_{t=0}^k(-2)^tM_t$ lies in the Bose–Mesner algebra of the Johnson scheme;
--   2. its eigenvalues are
--   $$\lambda_j=\binom nk^{-1}\sum_{t=j}^k(-2)^t\binom{k-j}{t-j}\binom{n-t-j}{k-t},\qquad 0\le j\le k,\qquad(27)$$
--   with $\lambda_j$ of multiplicity $d_j=\binom nj-\binom n{j-1}$;
--   3. the uniform vector $u$ is an eigenvector for $\lambda_0$;
--   4. $q=\lambda_0$, $\delta=0$, $\rho^+=\max_{1\le j\le k}\lambda_j$ (28), and $\rho^-=|\lambda_1|$.
--
--   These identities convert the abstract leakage parameters into explicit binomial sums, which Lemma 5.1 then estimates.
--
--   **Formalization Note** "Eigenvalues $\lambda_j$ with multiplicities $d_j$" is the factorization of the characteristic polynomial, $\det(X-\mathcal E)=\prod_{j=0}^k(X-\lambda_j)^{d_j}$. The maximum over $j\ge1$ is stated as a bound by every $\lambda_j$ that is attained.
--
--   Differences from the source:
--   - reading: (27)–(28) stated in §5.1 under "Throughout this section assume ℋ = ([n] k)", without their own hypotheses → the hypotheses of §5.1's Theorems 5.2, 5.3 and Lemma 5.1: n ⩾ k ⩾ 2 even, α = k²/n < 1/16; reason: (27) needs k ⩽ n/2 (Fact 3.1), and ρ⁺ = max_{j⩾1} λ_j and ρ⁻ = |λ_1| use Lemma 5.1 (λ_2 > 0, odd λ_j < 0 with |λ_1| largest), which needs α < 1/16
--   - generalization: (27)–(28) → (27)–(28) together with ℰ = (n k)^{−1} Σ_t (−2)^t M_t (p.33) and ρ⁻ = |λ_1| (p.36); reason: both extra conjuncts are statements of the same section; dropping them gives (27)–(28)
--   - encoding: λ_j occurs d_j times in spec(ℰ) → charpoly ℰ = Π_{j=0}^{k} (X − λ_j)^{d_j}; reason: the characteristic polynomial records the eigenvalues with multiplicity; ℰ is Hermitian
--   - encoding: ρ⁺ = max_{j⩾1} λ_j → every λ_j with 1 ⩽ j ⩽ k is ⩽ ρ⁺, and ρ⁺ = λ_j for some 1 ⩽ j ⩽ k; reason: the maximum of a finite nonempty family is the attained upper bound; λ_j is defined only for j ⩽ k
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, eqs. (27)–(28), pp.33–34; 'Note that ρ− = |λ1|', proof of Theorem 5.3, p.36

import Mathlib
import Definitions.Def_SYKEdge_Johnson
import Definitions.Def_SYKEdge_SignMatrix
open Matrix Polynomial

namespace SYKEdge

/-- **Eqs. (27)–(28)** and `ρ⁻ = |λ₁|`, A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, pp.33–34 and the proof of Theorem 5.3, p.36.

For the dense hypergraph `H = ([n] choose k)` (`n ⩾ k ⩾ 2` even, `α = k²/n < 1/16`):
`ℰ = (n choose k)^{−1} Σ_{t=0}^{k} (−2)^t M_t`; the eigenvalues of `ℰ` are the `λ_j` of (27),
`0 ⩽ j ⩽ k`, with `λ_j` occurring `d_j = (n choose j) − (n choose j−1)` times; `u` is an eigenvector for
`λ₀`; and `q = λ₀`, `δ = 0`, `ρ⁺ = max_{j⩾1} λ_j` (28), and `ρ⁻ = |λ₁|` (p.36).

**Formalization Note.** The hyperedges are indexed by the `k`-subsets themselves (`S = Subtype.val`).
"`λ_j` occurs `d_j` times in `spec(ℰ)`" is the factorization of the characteristic polynomial
`Π_j (X − λ_j)^{d_j}`. `max_{j⩾1} λ_j` is the maximum over `1 ⩽ j ⩽ k`, stated as "an upper bound
that is attained". -/
theorem eq_27_28 (n k : ℕ) (hn : Even n) (hk : Even k) (h2k : 2 ≤ k) (hkn : k ≤ n)
    (hα : (k : ℝ) ^ 2 / n < 1 / 16) :
    signMat (Subtype.val : KSet n k → Finset (Fin n)) =
        (((n.choose k : ℕ) : ℂ))⁻¹ • ∑ t ∈ Finset.range (k + 1), ((-2 : ℂ) ^ t) • johnsonM n k t ∧
    (signMat (Subtype.val : KSet n k → Finset (Fin n))).charpoly =
        ∏ j ∈ Finset.range (k + 1), (X - C ((lamJ n k j : ℝ) : ℂ)) ^ dJ n j ∧
    signMat (Subtype.val : KSet n k → Finset (Fin n)) *ᵥ uVec (KSet n k) =
        ((lamJ n k 0 : ℝ) : ℂ) • uVec (KSet n k) ∧
    qParam (Subtype.val : KSet n k → Finset (Fin n)) = lamJ n k 0 ∧
    deltaParam (Subtype.val : KSet n k → Finset (Fin n)) = 0 ∧
    (∀ j ∈ Finset.Icc 1 k, lamJ n k j ≤ rhoPlus (Subtype.val : KSet n k → Finset (Fin n))) ∧
    (∃ j ∈ Finset.Icc 1 k, rhoPlus (Subtype.val : KSet n k → Finset (Fin n)) = lamJ n k j) ∧
    rhoMinus (Subtype.val : KSet n k → Finset (Fin n)) = |lamJ n k 1| := by sorry

end SYKEdge
