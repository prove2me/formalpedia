-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_theorem_2_3
-- name    : SparseLpLq.SmallP.Supplement.theorem_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:12:52.91291+00:00
-- url     : https://prove2.me/theorems/2d69e4c5-82e9-4d7a-bafe-549e3952cc71
-- title:
--   Theorem 2.3 (corrected: λ* in r of (2.6) replaced by λ̂ = min λ_min(A_ℐᵀA_ℐ) over full-column-rank A_ℐ) — with p* of (2.9), SOL(A,b,σ,p,1) ⊆ SOL(A,b,σ,0,1) for every p ∈ (0,p*)
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and the blanket assumptions of the paper (p. 1) hold for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)=\{x:\|Ax-b\|_1\le\sigma\}\neq\emptyset$ and $\|b\|_1>\sigma$.
--
--   Let $\hat\lambda$ be the least value of $\lambda_{\min}(A_{\mathcal I}^\top A_{\mathcal I})$ over the nonempty column subsets $\mathcal I$ for which $A_{\mathcal I}$ has full column rank, $r:=(\sigma+\|b\|_2)/\sqrt{\hat\lambda}$, $\tilde r$ the smallest nonzero $|x_i|$ over all extreme points $x$ of the polyhedra $\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1)$, $j=1,\dots,2^n$ (2.7), and $s$ the optimal value of problem (1.4) with $p=0$ (the least $\|x\|_0$ over $\mathrm{FEA}(A,b,\sigma,1)$). Put
--   $$p^*:=\min\Big\{1,\ \frac{\ln(s+1)-\ln s}{\ln r-\ln\tilde r}\Big\}. \tag{2.9}$$
--   Then for every $p\in(0,p^*)$,
--   $$\mathrm{SOL}(A,b,\sigma,p,1)\subseteq\mathrm{SOL}(A,b,\sigma,0,1),$$
--   that is, every minimizer of $\|x\|_p^p$ subject to $\|Ax-b\|_1\le\sigma$ is a sparsest feasible point.
--
--   This is a computable version of the first part of Theorem 2.2: the threshold $p^*$ is expressed through the data $A,b,\sigma$ alone.
--
--   **Formalization Note** The paper defines $r$ in (2.6) with $\lambda^*$, the smallest nonzero eigenvalue of $A^\top A$, and its step (2.8) claims $\lambda_{\min}(A_{\mathcal I}^\top A_{\mathcal I})\ge\lambda^*$ for every full-column-rank $A_{\mathcal I}$. That claim, and Theorem 2.3 with the printed $r$, are false: for $A=\begin{pmatrix}0.01&1&0\\0&1&1\end{pmatrix}$, $b=(1,0)^\top$, $\sigma=0$ the blanket assumptions hold, $s=1$, $\tilde r=1$, $\lambda^*\approx0.382$, $r\approx1.618$ and the printed $p^*=1$, yet for $p=1/2$ the unique minimizer is $(0,1,-1)$ (value $2$, against $10$ at the only $1$-sparse feasible point $(100,0,0)$), which is not sparsest. Replacing $\lambda^*$ by $\hat\lambda$ is exactly what the proof's step (2.8) uses, so the paper's argument then goes through unchanged; when $A$ has full column rank $\hat\lambda=\lambda^*$ and the statement is the printed one. $\hat\lambda$, $\tilde r$ and $s$ are infima of sets that are finite and nonempty under the blanket assumptions, hence minima. When $r=\tilde r$ the quotient in (2.9) has a zero denominator and a positive numerator; it is read as $+\infty$, so $p^*=1$ (the proof, p. 10, notes that (2.10) then holds for every $p\in(0,1)$). Orthants are indexed by sign patterns.
--
--   Differences from the source:
--   - correction: r := (σ + ‖b‖₂)/√λ* with λ* the smallest nonzero eigenvalue of AᵀA (2.6) → r := (σ + ‖b‖₂)/√λ̂ with λ̂ = min of λ_min(A_ℐᵀA_ℐ) over nonempty ℐ with rank A_ℐ = |ℐ| (lamHat); reason: the printed theorem is false — A = [[0.01,1,0],[0,1,1]], b = (1,0), σ = 0 satisfy the blanket assumptions, give s = 1, r̃ = 1, r ≈ 1.618, p* = 1, while SOL(A,b,σ,1/2,1) = {(0,1,−1)} is not sparsest; λ̂ is the bound the proof's step (2.8) uses, and λ̂ = λ* when A has full column rank
--   - reading: p* = min{1, (ln(s+1) − ln s)/(ln r − ln r̃)} with ln r − ln r̃ = 0 when r = r̃ → pStar := 1 if r = r̃, else the printed formula; reason: the quotient has a positive numerator and a zero denominator, read as +∞; the proof on p. 10 treats r/r̃ = 1 as (2.10) holding for every p ∈ (0,1); Lean's x/0 = 0 would otherwise make p* = 0 and the theorem vacuous
--   - encoding: λ̂, r̃ and s as minima → sInf of the finite set of least spectrum points of A_ℐᵀA_ℐ, of the set in (2.7), and of lpObj 0 '' FEA(A,b,σ,1); reason: each set is finite (or a set of naturals) and nonempty under the blanket assumptions, so the infimum is the minimum
--   - encoding: orthants ℙ_j, j = 1, …, 2ⁿ; EXT → sign patterns s : Fin n → Bool (base orthant); Set.extremePoints ℝ; reason: one-to-one enumeration of the closed orthants; EXT is the set of extreme points
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 10, Theorem 2.3 and (2.9); constants (2.6)–(2.7) and step (2.8) p. 9; proof p. 10

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Constants

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem theorem_2_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∀ p ∈ Set.Ioo (0 : ℝ) (pStar A b σ), SOL A b σ p 1 ⊆ SOL A b σ 0 1 := by sorry
end SparseLpLq.SmallP.Supplement
