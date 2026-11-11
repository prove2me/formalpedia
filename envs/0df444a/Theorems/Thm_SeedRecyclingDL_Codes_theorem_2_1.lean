-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_theorem_2_1
-- name    : SeedRecyclingDL.Codes.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:09.728576+00:00
-- url     : https://prove2.me/theorems/d06f55b1-6bec-49c0-8043-e530bd3c7d8c
-- title:
--   Theorem 2.1 — Seed recycling
-- statement:
--   Let $m,L\ge1$, and let each $m$-bit string $x$ have a competitor set $\Gamma(x)$ of size at most $L$ excluding $x$. Suppose $2^b\ge2L\lceil m/b\rceil$, $2^r\ge2L$, and $1\le r\le b$. The actual recycled tag has length $2b+r$, separates $x$ from every $x'\in\Gamma(x)$ for all four rank-message blocks, and is injective in $(\sigma,\tau)$ for each fixed $x$. The defined rank decoder recovers both blocks from $x$ and its tag.
--   $$\text{message bits}=2b-2,\qquad\text{net tag cost}=r+2.$$
--   If $r=\lceil\log_2(2L)\rceil$, the net cost is strictly less than $\log_2L+4$. No symmetry of $\Gamma$ is required. This gives a separating tag whose two seeds also carry information.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Theorem 2.1, printed p. 7 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem theorem_2_1 {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (hp : P.p = 2) (m L r : ℕ) (Γ : Competitors)
    (hΓ : ValidCompetitors m L Γ) (hpar : ValidParameters m L P.k r) :
    (∀ x sigma tau : Word, x.length = m → sigma.length = P.k - 1 →
      tau.length = P.k - 1 → (tag P m r Γ x sigma tau).length = 2 * P.k + r) ∧
    (∀ x x' sigma tau sigma' tau' : Word,
      x.length = m → x' ∈ Γ x → sigma.length = P.k - 1 → tau.length = P.k - 1 →
      sigma'.length = P.k - 1 → tau'.length = P.k - 1 →
      tag P m r Γ x sigma tau ≠ tag P m r Γ x' sigma' tau') ∧
    (∀ x sigma tau : Word, x.length = m → sigma.length = P.k - 1 →
      tau.length = P.k - 1 →
      recoverRanks P m r Γ x (tag P m r Γ x sigma tau) = some (sigma, tau)) ∧
    (∀ x sigma tau sigma' tau' : Word,
      x.length = m → sigma.length = P.k - 1 → tau.length = P.k - 1 →
      sigma'.length = P.k - 1 → tau'.length = P.k - 1 →
      tag P m r Γ x sigma tau = tag P m r Γ x sigma' tau' → sigma = sigma' ∧ tau = tau') ∧
    ((2 * P.k + r : ℕ) : ℤ) - (2 * (P.k - 1) : ℕ) = (r + 2 : ℕ) ∧
    (r = EditMulticoloring.Code.ceilLog 2 (2 * L) → (r + 2 : ℝ) < log₂ L + 4)
    := by sorry

end SeedRecyclingDL.Codes
