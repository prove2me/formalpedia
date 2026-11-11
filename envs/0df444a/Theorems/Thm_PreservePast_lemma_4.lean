-- Prove2me | Theorems.Thm_PreservePast_lemma_4
-- name    : PreservePast.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:49.634981+00:00
-- url     : https://prove2.me/theorems/b6f52118-b0cd-43f2-b7ff-81bb56c964eb
-- title:
--   Lemma 4 — a multiscale nuclear-ball code
-- statement:
--   Let $a_0,b_0\ge0$, $k=\min(a_0,b_0)$, $L\ge0$, $\delta>0$ and $p\in\{1,2\}$, and let $N_p(a_0,b_0,L,\delta)$ be the code length (41) (with $N_p=0$ if $\delta\ge L$).
--
--   1. There is a deterministic code with $N_p(a_0,b_0,L,\delta)$ bits for the nuclear ball $\{A\in\mathbb R^{a_0\times b_0}:\|A\|_*\le L\}$: an encoder $\mathrm{enc}$ into $\{0,\dots,2^{N_p}-1\}$ and a decoder $\mathrm{dec}$ with
--   $$
--   \|\mathrm{dec}(\mathrm{enc}(A))-A\|\le\delta\qquad\text{whenever }\|A\|_*\le L,
--   $$
--   the error measured in the operator norm for $p=1$ and in the Frobenius norm for $p=2$.
--   2. There is an absolute constant $C$ such that, for $z=L/\delta>1$,
--   $$
--   N_p(a_0,b_0,L,\delta)\le C(a_0+b_0+1)E_p(k,z),\qquad E_p(k,z)=\begin{cases}z^p,&1<z\le k^{1/p},\\ k\log_2(2+z/k^{1/p}),&z>k^{1/p}.\end{cases}
--   $$
--
--   The code quantizes the covariance and the gradient of an old task in Theorem 9 and in the finite execution of the upper bound.
--
--   **Formalization Note** A deterministic public code with $N$ bits is a pair of functions $\mathbb R^{a_0\times b_0}\to\{0,\dots,2^N-1\}\to\mathbb R^{a_0\times b_0}$. The constant $C$ is chosen before $p,a_0,b_0,L,\delta$.
--
--   Differences from the source:
--   - encoding: a deterministic public code achieves error at most δ using N_p bits → ∃ enc : ℝ^{a₀×b₀} → Fin (2^{N_p}), dec, with reconstruction error ≤ δ on the nuclear ball; reason: the definition of a code; same content
--   - encoding: J = ⌊log₂ h⌋, r_j = min{2^j, h − 2^j + 1} → `Nat.log 2 h`, r_j computed in ℤ; reason: Lean convention; equal for h ≥ 1, and the degenerate k = 0 case gives N_p = 0
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19), Lemma 4, (41)–(42)

import Mathlib
import Definitions.Def_PreservePast_Ncode
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace PreservePast

/-- **Lemma 4 (a multiscale nuclear-ball code).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19): "Let
A ∈ ℝ^{a₀×b₀} satisfy ‖A‖_* ≤ L, where L ≥ 0, and put k = min(a₀, b₀). For p = 1 measure
reconstruction error in operator norm, and for p = 2 measure it in Frobenius norm. For δ > 0, a
deterministic public code achieves error at most δ using N_p(a₀, b₀, L, δ) bits, where N_p = 0 if
δ ≥ L. … One may take N_p(a₀, b₀, L, δ) = ⌈(a₀ + b₀ + 1) Σ_{j=0}^{J} r_j log₂(1 + 6S_j/η_j)⌉. (41)
For z = L/δ > 1, define E_p(k, z) … There is an absolute constant C such that
N_p(a₀, b₀, L, δ) ≤ C(a₀ + b₀ + 1)E_p(k, z). (42)"

(i) For `p ∈ {1, 2}`, `L ≥ 0` and `δ > 0` there are an encoder of the nuclear ball into
`2^{N_p}` messages and a decoder with reconstruction error at most `δ` (operator norm for `p = 1`,
Frobenius norm for `p = 2`). (ii) (42), with `C` chosen before all parameters.

**Formalization Note.** A "deterministic public code using N bits" is a pair
`enc : ℝ^{a₀×b₀} → Fin (2^N)`, `dec : Fin (2^N) → ℝ^{a₀×b₀}`. -/
theorem lemma_4 :
    (∀ (p a₀ b₀ : ℕ) (L δ : ℝ), (p = 1 ∨ p = 2) → 0 ≤ L → 0 < δ →
      ∃ (enc : Matrix (Fin a₀) (Fin b₀) ℝ → Fin (2 ^ Ncode p a₀ b₀ L δ))
        (dec : Fin (2 ^ Ncode p a₀ b₀ L δ) → Matrix (Fin a₀) (Fin b₀) ℝ),
        ∀ A, WainwrightHDS.NucNorm.nucNorm A ≤ L → codeErr p (dec (enc A) - A) ≤ δ) ∧
    ∃ C : ℝ, ∀ (p a₀ b₀ : ℕ) (L δ : ℝ), (p = 1 ∨ p = 2) → 0 ≤ L → 0 < δ → 1 < L / δ →
      (Ncode p a₀ b₀ L δ : ℝ) ≤ C * ((a₀ : ℝ) + b₀ + 1) * Ecode p (min a₀ b₀) (L / δ) := by sorry

end PreservePast
