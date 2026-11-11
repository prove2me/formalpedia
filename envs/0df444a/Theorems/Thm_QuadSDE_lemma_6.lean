-- Prove2me | Theorems.Thm_QuadSDE_lemma_6
-- name    : QuadSDE.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:42.036583+00:00
-- url     : https://prove2.me/theorems/6184694b-14b5-4d89-8830-769adbdb3ce6
-- title:
--   Lemma 6 — $\|\psi_L(t)\|_S^2\le R_*^2e^{-\lambda_*t}$ and $\int_0^T\sum_nne^{2S(n)}\|Q_n\psi_L\|^2\le R_*^2/\lambda_*$
-- statement:
--   Let the drift be admissible with strength at most $J>0$ and at most $r\ge1$ channels, $0<p,q\le1$, $T\ge0$, $Y\in\mathbb R^N$, and $L\ge1$. Let $\lambda_*=q/(2\rho(T))$, $R_*=\sqrt{e^{2\|y\|^2}-1}$, $\theta$ and $S(n)=2\theta(\sqrt n-1)$ as in (38), and $\|v\|_S^2=\sum_{n\ge1}e^{2S(n)}\|Q_nv\|^2$.
--   1. Every solution $\psi_L$ of the projected evolution (36) with cutoff $L$ satisfies, for $t\in[0,T]$,
--   $$\|\psi_L(t)\|_S^2\le R_*^2e^{-\lambda_*t}\qquad(41),\qquad\int_0^T\sum_{n=1}^Lne^{2S(n)}\|Q_n\psi_L(t)\|^2\,dt\le\frac{R_*^2}{\lambda_*}\qquad(42).$$
--   2. The same inequalities hold for modified coefficients: for every $T'\in[0,T]$, all functions $\tilde\lambda,\tilde\sigma$ with $\tilde\lambda(t)\ge\lambda_*$ and $|\tilde\sigma(t)|\le\sqrt{\rho(T)}$ on $[0,T']$, and every solution $v$ in $\mathcal H_L$ of $v'=\Pi_L\big(-\tilde\lambda(t)M+\tilde\sigma(t)C_0\big)\Pi_Lv$ on $[0,T']$,
--   $$\|v(t)\|_S^2\le\|v(0)\|_S^2e^{-\lambda_*t}\quad(t\in[0,T']),\qquad\int_0^{T'}\sum_{n=1}^Lne^{2S(n)}\|Q_nv(t)\|^2\,dt\le\frac{\|v(0)\|_S^2}{\lambda_*}.$$
--   In particular this covers $C$ replaced by $-C$ ($\tilde\sigma=-\sqrt\rho$) and the time dependence of $A$ and $C$ reversed on any subinterval $[a,b]$ ($\tilde\lambda(t)=\lambda(a+b-t)$, $\tilde\sigma(t)=\sqrt{\rho(a+b-t)}$ on $[0,b-a]$).
--
--   The weighted decay is uniform in the cutoff $L$; it drives the projection-error bound of Theorem 3 and the identification of Lemma 7.
--
--   Differences from the source:
--   - generalization: The same inequality holds with C replaced by −C, and with the time dependence of A and C reversed on any subinterval of [0, T] → clause 2: any coefficient functions λ̃ ≥ λ_* and |σ̃| ≤ √ρ(T) on any [0, T'] ⊆ [0, T], any solution v in 𝓗_L, with ‖v(0)‖²_S in place of R²_*; reason: p. 22: the proof uses only these bounds; −C and reversal on [a, b] (shifted to [0, b − a]) are special cases, and v(0) = Π_L ψ(0) gives ‖v(0)‖²_S ≤ R²_* by (40)
--   - generalization: the projected solutions (36) for every finite cutoff L → every solution of (36) with cutoff L ≥ 1; reason: (36) has a unique solution; (35)–(36) are set up for k ≥ 2, and L = 1 adds a further finite cutoff, so the statement contains the source's
--   - encoding: ‖·‖_S² and the time integral → weighted sum in [0, ∞]; interval integral of a continuous function; ℓ² derivatives, one-sided at the endpoints; reason: Lean convention; no junk values
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.3, Lemma 6, p. 21

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_Fock
import Definitions.Def_QuadSDE_Kolmogorian

open scoped ENNReal

namespace QuadSDE

/-- **Lemma 6 (weighted decay of the projected solutions).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.3, Lemma 6, p. 21: "For
every finite cutoff `L`, the projected solutions satisfy `‖ψ_L(t)‖²_S ≤ R²_* e^{−λ_* t}`, (41)
`∫_0^T Σ_{n=1}^L n e^{2S(n)} ‖Q_n ψ_L(t)‖² dt ≤ R²_*/λ_*`. (42) The same inequality holds with `C`
replaced by `−C`, and with the time dependence of `A` and `C` reversed on any subinterval of
`[0, T]`."

Let the drift be admissible with strength at most `J > 0` and at most `r ≥ 1` channels, let
`0 < p, q ≤ 1`, `T ≥ 0`, `Y ∈ ℝ^N`, and let `L ≥ 1`. With `λ_* = q/(2ρ(T))`,
`R_* = (e^{2‖y‖²} − 1)^{1/2}`, `θ` and `S(n) = 2θ(√n − 1)` from Eq. (38) and the weighted norm
`‖v‖²_S = Σ_{n≥1} e^{2S(n)}‖Q_n v‖²` (39):
1. (Eqs. (41)–(42)) every solution `ψ_L` of the projected evolution (36) with cutoff `L` satisfies
   `‖ψ_L(t)‖²_S ≤ R²_* e^{−λ_* t}` for `t ∈ [0, T]` and
   `∫_0^T Σ_{n=1}^L n e^{2S(n)} ‖Q_n ψ_L(t)‖² dt ≤ R²_*/λ_*`;
2. (the same inequalities for modified coefficients) for every horizon `T' ∈ [0, T]`, all
   coefficient functions `λ̃, σ̃` with `λ̃(t) ≥ λ_*` and `|σ̃(t)| ≤ √ρ(T)` on `[0, T']`, and every
   solution `v` in `𝓗_L` of `v′ = Π_L(−λ̃(t) M + σ̃(t) C₀)Π_L v` on `[0, T']`:
   `‖v(t)‖²_S ≤ ‖v(0)‖²_S e^{−λ_* t}` for `t ∈ [0, T']` and
   `∫_0^{T'} Σ_{n=1}^L n e^{2S(n)} ‖Q_n v(t)‖² dt ≤ ‖v(0)‖²_S/λ_*`.

**Formalization Note.** Clause 2 is the general form of the lemma's last sentence, as its proof
gives it (p. 22: "The proof uses only the norm bounds on the couplings and the lower bound on
`λ(t)`"): `C → −C` is `σ̃ = −√ρ`, and reversing `A` and `C` on a subinterval `[a, b]` is
`λ̃(t) = λ(a + b − t)`, `σ̃(t) = √ρ(a + b − t)` on `[0, b − a]`. Weighted norms are summed in
`ℝ≥0∞`; the time integrals are of continuous functions on `[0, T]`. -/
theorem lemma_6 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (J : ℝ) (hJ0 : 0 < J)
    (hJ : strengthLE c J) (r : ℕ) (hr0 : 1 ≤ r) (hr : channelsLE c r) (p q T : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (Y : Fin N → ℝ) (L : ℕ) (hL : 1 ≤ L) :
    (∀ ψL : ℝ → Fock N, IsProjSol c p q Y T L ψL →
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        wNormSq (theta J r p q T) ⇑(ψL t) ≤
          ENNReal.ofReal (Rstar p Y ^ 2 * Real.exp (-(lamStar p q T * t)))) ∧
      ∫ t in (0 : ℝ)..T, ∑ n ∈ Finset.Icc 1 L,
          (n : ℝ) * Real.exp (2 * Sexp (theta J r p q T) n) * degNormSq n ⇑(ψL t)
        ≤ Rstar p Y ^ 2 / lamStar p q T) ∧
    ∀ (T' : ℝ), 0 ≤ T' → T' ≤ T → ∀ (lt st : ℝ → ℝ),
      (∀ t ∈ Set.Icc (0 : ℝ) T', lamStar p q T ≤ lt t ∧ |st t| ≤ Real.sqrt (rho p q T)) →
      ∀ v : ℝ → Fock N,
        (∀ t (m : MIdx N), ¬ (1 ≤ mdeg m ∧ mdeg m ≤ L) → v t m = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) T', ∃ w : Fock N,
          ⇑w = Pik L (fun m => -((lt t : ℝ) : ℂ) * numOp (Pik L ⇑(v t)) m +
            ((st t : ℝ) : ℂ) * C0 c (Pik L ⇑(v t)) m) ∧
          HasDerivWithinAt v w (Set.Icc 0 T') t) →
        (∀ t ∈ Set.Icc (0 : ℝ) T',
          wNormSq (theta J r p q T) ⇑(v t) ≤
            wNormSq (theta J r p q T) ⇑(v 0) * ENNReal.ofReal (Real.exp (-(lamStar p q T * t)))) ∧
        ENNReal.ofReal (∫ t in (0 : ℝ)..T', ∑ n ∈ Finset.Icc 1 L,
            (n : ℝ) * Real.exp (2 * Sexp (theta J r p q T) n) * degNormSq n ⇑(v t))
          ≤ wNormSq (theta J r p q T) ⇑(v 0) / ENNReal.ofReal (lamStar p q T) := by sorry

end QuadSDE
