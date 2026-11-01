-- Prove2me | Theorems.Thm_TucciCIT_eq_2_5_svd
-- name    : TucciCIT.eq_2_5_svd
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:23.574609+00:00
-- url     : https://prove2.me/theorems/d7b76392-aef8-403e-aa14-c680e2fc37b4
-- title:
--   Eqs. (2.5)–(2.6) — rectangular singular value decomposition
-- statement:
--   Assume $N_x \le N_y$, as the paper does on p. 3. For every rectangular matrix $\psi$ with rows indexed by $S_x$ and columns by $S_y$ there exist
--
--   - an injection $e : S_x \hookrightarrow S_y$ (identifying the row index $x$ with the column index $y = x$),
--   - unitary matrices $U$ on $\mathcal H_x$ and $V$ on $\mathcal H_y$,
--   - numbers $p_x \ge 0$,
--
--   such that
--
--   1. $\tilde\psi = U\psi V^\dagger$ is "diagonal": $\tilde\psi_{xy} = \sqrt{p_x}$ if $y = e(x)$ and $\tilde\psi_{xy} = 0$ otherwise;
--   2. $U\psi\psi^\dagger U^\dagger = \tilde\psi\tilde\psi^\dagger = \operatorname{diag}(p_x)$;
--   3. if $\sum_{x,y}|\psi_{xy}|^2 = 1$, then $\sum_x p_x = 1$.
--
--   This is the Singular Value Decomposition (equivalently, the Schmidt representation (2.8)) on which the value of $E_F$ and the attainment part of the main theorem rest.
--
--   Differences from the source:
--   - encoding: ψ̃xy = 0 if x ≠ y, with rows and columns both numbered from 0 and Nx ≤ Ny → ψ̃ supported on the graph of an injection e : X ↪ Y; reason: X and Y are unordered finite types; an injection is the identification of the first Nx columns with the rows
--   - generalization: ψ̃ diagonal → ψ̃ diagonal with real nonnegative diagonal entries √p_x; reason: a stronger conclusion that implies the source's; it is the Schmidt form (2.8), p.4
--   - generalization: ψ normalized (Σ|ψxy|² = 1) → any ψ, with Σ p_x = 1 concluded under the normalization; reason: the decomposition exists for every matrix; it specializes to the source's normalized ψ
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eqs. (2.5)–(2.6) and the following sentence, p.3

import Mathlib

open scoped Matrix

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eqs. (2.5)–(2.6), p.3 (PDF p.3): "There always exist unitary matrices
U and V such the UψV† = ψ̃, where the rectangular matrix ψ̃ is “diagonal”, in the sense that
ψ̃xy = 0 if x ≠ y. … Define pi for 0 ≤ i ≤ Nx − 1 by Uψψ†U† = ψ̃ψ̃† = diag(p0, p1, …, pNx−1).
… the pi's are non-negative numbers. Furthermore, since tr(Uψψ†U†) = Σx,y |ψxy|² = 1, the
pi's add up to one."

Rectangular singular value decomposition. Assume `N_x ≤ N_y` (the paper's standing assumption,
p.3). For every `ψ : Matrix X Y ℂ` there are an injection `e : S_x ↪ S_y` (the paper's
identification of the row index `x` with the column index `y = x`), unitaries `U`, `V` and
numbers `p_x ≥ 0` such that
1. `(UψV†)_{xy} = √p_x` if `y = e(x)` and `0` otherwise (so `ψ̃ = UψV†` is "diagonal");
2. `Uψψ†U† = diag(p_x)`;
3. if `Σ_{x,y} |ψ_{xy}|² = 1`, then `Σ_x p_x = 1`.

**Formalization Note.** "Diagonal" for a rectangular matrix with `N_x ≤ N_y` means supported on
the graph of the embedding `e`; the paper writes `x = y`. The diagonal entries are taken real and
nonnegative, `√p_x` (as in the Schmidt form (2.8), p.4). -/
theorem eq_2_5_svd {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (hXY : Fintype.card X ≤ Fintype.card Y) (ψ : Matrix X Y ℂ) :
    ∃ (e : X ↪ Y) (U : Matrix.unitaryGroup X ℂ) (V : Matrix.unitaryGroup Y ℂ) (p : X → ℝ),
      (∀ x, 0 ≤ p x) ∧
      (∀ x y, ((U : Matrix X X ℂ) * ψ * (V : Matrix Y Y ℂ)ᴴ) x y =
        if y = e x then ((Real.sqrt (p x) : ℝ) : ℂ) else 0) ∧
      (U : Matrix X X ℂ) * (ψ * ψᴴ) * (U : Matrix X X ℂ)ᴴ =
        Matrix.diagonal (fun x => ((p x : ℝ) : ℂ)) ∧
      ((∑ x, ∑ y, ‖ψ x y‖ ^ 2 = 1) → ∑ x, p x = 1) := by sorry

end TucciCIT
