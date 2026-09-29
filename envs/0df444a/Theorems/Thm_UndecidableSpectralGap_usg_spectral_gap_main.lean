-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_spectral_gap_main
-- name    : UndecidableSpectralGap.usg_spectral_gap_main
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T05:44:21.468656+00:00
-- url     : https://prove2.me/theorems/3c51b3bf-00b5-4bf6-88ae-d35e9c498299
-- title:
--   Theorem 3 - undecidability of the spectral gap (main theorem)
-- statement:
--   **Main theorem.** Fix a universal Turing machine and let $\varepsilon>0$. One can construct explicitly a local Hilbert space dimension $d$, matrices $A,A',B,C,D,D'$ of size $d^2\times d^2$, a diagonal projector $\Pi$ of size $d\times d$, and a rational $\beta$ with $0<\beta<\varepsilon$, such that
--
--   1. $A$ is diagonal with entries in $\mathbb{Z}$;
--   2. $A'$ is Hermitian with entries in $\mathbb{Z}+\tfrac1{\sqrt2}\mathbb{Z}$;
--   3. $B$ and $C$ have entries in $\mathbb{Z}$;
--   4. $D$ is diagonal with entries in $\mathbb{Z}$;
--   5. $D'$ is Hermitian with entries in $\mathbb{Z}$;
--
--   and such that, for each natural number $n$, with $\varphi=\varphi(n)$ the rational whose binary expansion after the point is the binary expansion of $n$ reversed, $|\varphi|$ its number of digits, and $\alpha(n)$ an algebraic number with $\alpha(n)\le2\beta$, the interactions
--
--   $$h_1(n)=\alpha(n)\Pi,\qquad h_{\mathrm{col}}(n)=D+\beta D',$$
--   $$h_{\mathrm{row}}(n)=A+\beta\Bigl(A'+e^{i\pi\varphi}B+e^{-i\pi\varphi}B^{\dagger}+e^{i\pi2^{-|\varphi|}}C+e^{-i\pi2^{-|\varphi|}}C^{\dagger}\Bigr)$$
--
--   satisfy:
--
--   1. the local interaction strength is bounded by $1$, i.e. $\max\{\lVert h_1(n)\rVert,\lVert h_{\mathrm{row}}(n)\rVert,\lVert h_{\mathrm{col}}(n)\rVert\}\le1$;
--
--   2. if the universal machine halts on input $n$, the family $\{H^{\Lambda(L)}(n)\}_L$ on the square lattice with open boundary conditions is **gapped** in the strong sense, with gap $\gamma\ge1$: the ground state is non-degenerate and $\Delta(H^{\Lambda(L)}(n))\ge1$ for all sufficiently large $L$;
--
--   3. if it does not halt on input $n$, the family is **gapless** in the strong sense: there is $c>0$ such that for every $\varepsilon'>0$ and all sufficiently large $L$, every point of $[\lambda_0(H^{\Lambda(L)}(n)),\lambda_0(H^{\Lambda(L)}(n))+c]$ lies within $\varepsilon'$ of the spectrum.
--
--   Because the halting problem is undecidable, no algorithm determines whether an arbitrary such model is gapped or gapless, even at fixed local dimension $d$ and even under the promise that exactly one of the two strong alternatives holds. Since $\beta$ can be taken arbitrarily small, the whole family consists of arbitrarily small quantum perturbations of the classical model $h_{\mathrm{row}}=A$, $h_{\mathrm{col}}=D$, and the only dependence on $n$ sits in the prefactors $\alpha(n)$, $e^{i\pi\varphi(n)}$ and $e^{i\pi2^{-|\varphi(n)|}}$ of a fixed set of matrices.
--
--   **Formalization note.** The universal machine is represented by a partial recursive code, and halting on input $n$ is definedness of its evaluation at $n$; the statement is asserted for every such code, which is stronger than for one fixed universal machine. The three interaction matrices are introduced by the displayed equations as hypotheses, so that the conclusions are stated about exactly the model of the source.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 1.2, p. 3, Theorem 3 (Main theorem), restated in Section 6.2, p. 96 (the restated version, with alpha(n) <= 2*beta, is the one formalized).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_spectral_gap_main (u : Nat.Partrec.Code) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (A A' B C D D' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (Pi : Matrix (Fin d) (Fin d) ℂ) (β : ℚ) (α : ℕ → ℝ),
      -- `β` is a rational number, as small as desired
      0 < β ∧ (β : ℝ) < ε ∧
      -- (i) `A` is diagonal with integer entries
      (∀ i j, i ≠ j → A i j = 0) ∧ (∀ i, ∃ a : ℤ, A i i = (a : ℂ)) ∧
      -- (ii) `A'` is Hermitian with entries in `ℤ + (1/√2) ℤ`
      A'.IsHermitian ∧
        (∀ i j, ∃ a b : ℤ, A' i j = (a : ℂ) + (b : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) ∧
      -- (iii) `B`, `C` have integer entries
      (∀ i j, ∃ a : ℤ, B i j = (a : ℂ)) ∧ (∀ i j, ∃ a : ℤ, C i j = (a : ℂ)) ∧
      -- (iv) `D` is diagonal with integer entries
      (∀ i j, i ≠ j → D i j = 0) ∧ (∀ i, ∃ a : ℤ, D i i = (a : ℂ)) ∧
      -- (v) `D'` is Hermitian with integer entries
      D'.IsHermitian ∧ (∀ i j, ∃ a : ℤ, D' i j = (a : ℂ)) ∧
      -- `Π` is a diagonal projector
      Pi.IsHermitian ∧ (∀ i j, i ≠ j → Pi i j = 0) ∧ Pi * Pi = Pi ∧
      -- `α(n)` is an algebraic number bounded by `2β`
      (∀ n, IsAlgebraic ℚ (α n) ∧ α n ≤ 2 * (β : ℝ)) ∧
      ∀ n : ℕ, ∀ (h1 : Matrix (Fin d) (Fin d) ℂ)
        (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        h1 = ((α n : ℝ) : ℂ) • Pi →
        hcol = D + ((β : ℝ) : ℂ) • D' →
        hrow = A + ((β : ℝ) : ℂ) •
          (A' + Complex.exp (Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ)) • B
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ))) • B.conjTranspose
            + Complex.exp (Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ))) • C
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ)))) • C.conjTranspose) →
        -- (i) the local interaction strength is bounded by 1
        localInteractionStrength h1 hrow hcol ≤ 1 ∧
        -- (ii) if `UTM` halts on input `n`, the family is gapped with gap at least 1
        ((u.eval n).Dom → GappedWithGap d h1 hrow hcol 1) ∧
        -- (iii) if `UTM` does not halt on input `n`, the family is gapless
        (¬ (u.eval n).Dom → Gapless d h1 hrow hcol) := by
  sorry

end UndecidableSpectralGap
