-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_Supplement_quadratic_design_code
-- name    : SubspaceEvasion312.Explicit.Supplement.quadratic_design_code
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:25.77432+00:00
-- url     : https://prove2.me/theorems/4ae5d3c0-a398-4ad2-8df4-a4cf8d143e8f
-- title:
--   Corollary 21 — Guruswami–Kopparty design codes of rate 1/(8r)
-- statement:
--   There are absolute constants $K,h$ such that for every finite field $\mathbb F_q$ there is one encoder program $P$ with the following property. For all integers $r\ge1$ and $n\ge2$ with $q>4nr$, there are an $\mathbb F_q$-additive code $C\subseteq(\mathbb F_q^{s})^n$ with $s=2r$, an encoder $\mathrm{Enc}:\mathbb F_q^k\to(\mathbb F_q^s)^n$ of $C$ ($\mathbb F_q$-linear, image $C$, $k=\dim C$) and a design function $\tau$ such that
--
--   $$\mathrm{rate}(C)\ge\frac1{8r},\qquad C\text{ is a }\tau\text{-subspace design},\qquad \tau(r)<\frac1{4r},$$
--
--   $C$ is $(r,0,\ell,\ell)$ subspace list-recoverable for every $\ell\in\mathbb N$, and $P$, given $r$, $n$ and a message $x$, outputs $\mathrm{Enc}(x)$ within charged time and word bound $K\,n\,(r+\lfloor\log_2 q\rfloor+2)^h$.
--
--   This is the Case A code family of Theorem 25: it works over fields that grow with $n$, as opposed to the constant-field families of Corollaries 18 and 19.
--
--   **Formalization Note** "Computed in time" is read as encodable in time (printed p. 7). Time is measured in the mission's published register machine (field operations one step, program size charged).
--
--   Differences from the source:
--   - reading: r ∈ N → 1 ≤ r; reason: the bounds 1/8r and 1/4r are undefined at r = 0
--   - reading: rate R ≥ 1/8r, τ(r) < 1/4r → 1/(8r) ≤ codeRate C, τ r < 1/(4r); reason: conventional reading of 1/8r; the 'in particular' needs τ(r) < 1/r
--   - reading: can be computed in time n · poly(r, log q) → one encoder program per field with inputs r, n; charged time and word bound K·n·(r + ⌊log₂ q⌋ + 2)^h with absolute K, h; reason: printed p. 7 calls a code encodable in time T when an encoder runs in time T; a generator matrix has Θ(r n²) entries and cannot be output in n·poly(r, log q) time
--   - encoding: explicit τ subspace-design additive code C ⊆ (F_q^s)^n, s = 2r → ∃ k, C : Code F (2r) n, E with IsEncoder C E, τ with SubspaceDesign C τ; reason: the mission's published definitions of encoders and subspace designs
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, Corollary 21, printed p. 11 (PDF p. 12); from Theorem 20 ([GK16]) and Lemma 14

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit.Supplement
open scoped ENNReal
/-- Corollary 21, printed p.11 (PDF p.12). One encoder program per field takes
r and n as inputs; its charged time, including program size, is K n (r + log q)^h
with absolute K and h. Every n >= 2 is covered, with no divisibility condition. -/
theorem quadratic_design_code :
    ∃ K h : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] [Fintype F], ∃ enc : Program F,
    ∀ r n : ℕ, 1 ≤ r → 2 ≤ n → 4 * n * r < Fintype.card F →
    ∃ (k : ℕ) (C : Code F (2 * r) n) (E : Vec F k →ₗ[F] Blocks F (2 * r) n)
      (τ : ℕ → ℝ),
      IsEncoder C E ∧ 1 / (8 * (r : ℝ)) ≤ codeRate C ∧
      SubspaceDesign C τ ∧ τ r < 1 / (4 * (r : ℝ)) ∧
      (∀ ℓ : ℕ, ListRecoverable C r 0 ℓ ℓ) ∧
      ∀ x : Vec F k, RunsWithin enc [r, n] (vectorData x)
        (K * n * (r + Nat.log 2 (Fintype.card F) + 2) ^ h)
        (K * n * (r + Nat.log 2 (Fintype.card F) + 2) ^ h) (blockData (E x)) := by sorry
end SubspaceEvasion312.Explicit.Supplement
