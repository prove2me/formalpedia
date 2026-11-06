-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_proposition_2_4
-- name    : SparseSDP.TwoSided.proposition_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:22.22681+00:00
-- url     : https://prove2.me/theorems/259117fe-362e-4b03-94dc-b3806f4a525e
-- title:
--   Proposition 2.4, pp. 19–20 — an approximate saddle point gives certificates and a primal solution
-- statement:
--   Let $C,A_1,\dots,A_m$ be Hermitian with $|b_j|\le R$ (Eq. (41)), $R,r\ge1$, $g\in[-R,R]$, and assume strong duality within the radii. Suppose $(Y^{\mathrm{out}},p^{\mathrm{out}})\in R\mathcal S_{n+1}\times\Delta_{m+1}$ has saddle-point gap at most $\xi$ for the target-value game. Then
--   $$
--   \ell_g\le s_g\le u_g\quad\text{and}\quad u_g-\ell_g\le\xi.
--   $$
--   Moreover:
--
--   1. If $g$ is attainable, then $s_g\ge0$ and $u_g\ge0$.
--   2. If $u_g\ge-\zeta$ for some $\zeta\ge0$, the leading $n\times n$ block $X^{\mathrm{out}}$ of $Y^{\mathrm{out}}$ satisfies $X^{\mathrm{out}}\succeq0$, $\operatorname{Tr}X^{\mathrm{out}}\le R$, $\langle C,X^{\mathrm{out}}\rangle\ge g-\xi-\zeta$, and $\langle A_j,X^{\mathrm{out}}\rangle\le b_j+\xi+\zeta$ for all $j$.
--   3. For every $\tau\ge0$, if $g\ge\mathrm{OPT}+(1+r)\tau$, then $s_g\le-\tau$.
--
--   This is what lets a game solver decide feasibility of a target value up to the accuracy $\Theta(\varepsilon/(1+r))$.
--
--   Differences from the source:
--   - generalization: the data of §2.6 (real symmetric after preprocessing, p. 18) → any `RCLike` scalar field; reason: the proof uses only Hermitian data; it specializes to $\mathbb R$ and to $\mathbb C$
--   - encoding: $s_g$ as a max–min → the real `sSup` `gameValue`; reason: the supremum is over a compact nonempty set, so it is the maximum
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Proposition 2.4, pp. 19–20, Eqs. (54)–(58)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Dall

open Matrix
open scoped ComplexOrder

namespace SparseSDP.TwoSided

/-- **Proposition 2.4** (Optimization-to-Feasibility Reduction), pp. 19–20.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Proposition 2.4, pp. 19–20.

Standing here: §2.6.1 (`|bⱼ| ≤ R`, Eq. (41), and `g ∈ [−R, R]`, §2.6.2), Hermitian data of norm at
most one. The gap of `(Y, p)` is that of the game with radii `R` and `1`. Item 3 uses strong
duality.

**Formalization Note.** Stated over `ℝ` and `ℂ` together; the solver uses the real case after
realification (§2.6.1, p. 18). -/
theorem proposition_2_4 {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} (I : Instance 𝕜 n m)
    (R r g ξ OPT : ℝ) (Y : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜) (p : Fin (m + 1) → ℝ)
    (hC : I.C.IsHermitian) (hA : ∀ j, (I.A j).IsHermitian) (hR : 1 ≤ R) (hr : 1 ≤ r)
    (hb : ∀ j, |I.b j| ≤ R) (hg : |g| ≤ R) (hSD : StrongDuality I R r OPT)
    (hY : Y ∈ (Spect R : Set (Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜)))
    (hp : p ∈ Simplex (m + 1) 1) (hgap : gap (Dall I R g) R 1 Y p ≤ ξ) :
    (lowCert I R g Y ≤ gameValue I R g ∧ gameValue I R g ≤ upCert I R g p ∧
      upCert I R g p - lowCert I R g Y ≤ ξ) ∧
    (Attainable I R g → 0 ≤ gameValue I R g ∧ 0 ≤ upCert I R g p) ∧
    (∀ ζ : ℝ, 0 ≤ ζ → -ζ ≤ upCert I R g p →
      Y.toBlocks₁₁.PosSemidef ∧ RCLike.re (Matrix.trace Y.toBlocks₁₁) ≤ R ∧
      g - ξ - ζ ≤ hs I.C Y.toBlocks₁₁ ∧
      ∀ j, hs (I.A j) Y.toBlocks₁₁ ≤ I.b j + ξ + ζ) ∧
    (∀ τ : ℝ, 0 ≤ τ → OPT + (1 + r) * τ ≤ g → gameValue I R g ≤ -τ) := by sorry

end SparseSDP.TwoSided
