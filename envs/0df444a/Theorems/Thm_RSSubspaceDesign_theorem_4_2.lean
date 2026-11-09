-- Prove2me | Theorems.Thm_RSSubspaceDesign_theorem_4_2
-- name    : RSSubspaceDesign.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:08.096194+00:00
-- url     : https://prove2.me/theorems/944140a3-2e91-4834-8537-d13818b274a8
-- title:
--   Theorem 4.2 — RS codes on effective points are $\tau$-subspace designs over $K$, $\tau(d)=\min\{1,\frac{k-1}{n}+\frac bn\log_2 d\}$
-- statement:
--   Let $K\subseteq F$ be finite fields and let $A=(\alpha_1,\dots,\alpha_n)$ be $(n,g,b,r)_{F,K}$-effective. For every $1\le k\le n$, the Reed–Solomon code
--   $$C=\mathrm{RS}_F(A,k)=\{(f(\alpha_1),\dots,f(\alpha_n)):f\in F[X]_{<k}\}$$
--   is a $\tau$-subspace-design code over $K$, with
--   $$\tau(d)=\min\Big\{1,\ \frac{k-1}{n}+\frac bn\log_2 d\Big\}\quad(1\le d\le r),\qquad\tau(d)=1\quad(d>r).\qquad(4.2)$$
--
--   With $b=\lceil n/g\rceil$ and $g$ large this is within $\varepsilon/4$ of the rate $k/n$ for all $d\le r$, which gives Theorem 1.1.
--
--   Differences from the source:
--   - encoding: distinct points α₁, …, αₙ; RS_F(A, k) as a K-additive code → an embedding α : Fin n ↪ F; the public ReedSolomon.code α k (evaluations of F[X]_{<k}) viewed over K by restrictScalars; reason: Lean convention; same code
--   - encoding: τ-subspace-design code (Definition 2.1, τ nondecreasing with values in [0, 1]) → IsSubspaceDesign, with no precondition on τ; τ given on all of ℕ (value at 0 unused); reason: the stated τ is nondecreasing with values in [0, 1] on d ≥ 1 (checked), so the claim is the same
--   - encoding: K ⊆ F finite fields; k − 1; log₂ → an algebra K → F with F finite; (k : ℝ) − 1; Real.logb 2; reason: K embeds in F, so it is finite; Lean conventions
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 4.2, p.18 (PDF p.20), display (4.2)

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_IsEffective

open Polynomial

namespace RSSubspaceDesign

/-- **Theorem 4.2 (Subspace-design bound).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Theorem 4.2 with display (4.2), p.18.

Let `K ⊆ F` be finite fields and `A = (α₁, …, αₙ)` be `(n, g, b, r)_{F,K}`-effective. For every
`1 ≤ k ≤ n`, the code `C = RS_F(A, k)` is a `τ`-subspace-design code over `K`, with
`τ(d) = min{1, (k − 1)/n + (b/n) log₂ d}` for `1 ≤ d ≤ r` and `τ(d) = 1` for `d > r`.

**Formalization Note.** The points are an embedding `α : Fin n ↪ F` (distinct), and `RS_F(A, k)` is
the public `ReedSolomon.code α k` (evaluations of `F[X]_{<k}`), an `F`-subspace of `Fⁿ`, viewed over
`K` by `restrictScalars K`. `K` is finite because it embeds in `F`. `τ` is given on all of `ℕ`;
its value at `0` is never used. -/
theorem theorem_4_2 {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]
    {n g b r : ℕ} (α : Fin n ↪ F) (hα : IsEffective K n g b r α) (k : ℕ) (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    IsSubspaceDesign K ((ReedSolomon.code α k).restrictScalars K)
      (fun d => if d ≤ r then min 1 (((k : ℝ) - 1) / n + (b : ℝ) / n * Real.logb 2 d) else 1) := by sorry

end RSSubspaceDesign
