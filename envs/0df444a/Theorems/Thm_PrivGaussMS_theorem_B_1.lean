-- Prove2me | Theorems.Thm_PrivGaussMS_theorem_B_1
-- name    : PrivGaussMS.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:10:18.510665+00:00
-- url     : https://prove2.me/theorems/0458d4f1-5cd3-4afb-94fb-496ce90e163b
-- title:
--   Theorem B.1 — an $(\varepsilon,\delta)$-DP mechanism releasing exactly $Q_P^{\otimes m}$ from $n=\lceil c[mL+(d+L)(\sqrt{mL}+L)/\varepsilon]\rceil$ Gaussian records in $O(n^3)$ operations
-- statement:
--   There are constants $c,A>0$ and one program $\mathsf P$ of the published sampling real RAM such that the following holds for all integers $d,m\ge1$, all $0<\alpha,\delta<1$ and $0<\varepsilon\le1$. Put
--   $$L=1+\log\frac{dm}{\alpha\delta\varepsilon},\qquad \eta=\frac{\alpha}{2m},\qquad Q_P=(1-\eta)P+\eta\,\mathcal N(0,I_d).$$
--   For every $n\ge\bigl\lceil c\bigl[mL+(d+L)(\sqrt{mL}+L)/\varepsilon\bigr]\bigr\rceil$, the mechanism $M$ that runs $\mathsf P$ on $n$ records of $\mathbb R^d$ (and on $d,m,n,\alpha,\delta,\varepsilon$) and releases $m$ vectors of $\mathbb R^d$ satisfies:
--
--   1. on every dataset and every random tape it halts within $A\,n^3$ operations;
--   2. its output is a jointly measurable function of the dataset and the tape;
--   3. it is $(\varepsilon,\delta)$-differentially private over all datasets;
--   4. for every $P=\mathcal N(\mu,\Sigma)$ with $\Sigma\succ0$, when $X\sim P^{\otimes n}$,
--   $$\mathcal L(M(X))=Q_P^{\otimes m},$$
--   the law including both input and mechanism randomness;
--   5. in particular $\mathrm{TV}(Q_P^{\otimes m},P^{\otimes m})\le\alpha/2$.
--
--   Running a single-sample mechanism $m$ times would need of order $md/\varepsilon$ records; this mechanism needs $d\sqrt m/\varepsilon$ in that term while keeping the $m$ outputs exactly independent.
--
--   **Formalization Note** The machine is `PolySampIso.Machine` (exact real arithmetic with rational literals, $\sqrt{\cdot}$, $\exp$, $\log$, $\mathcal N(0,1)$ and $\mathrm{Exp}(1)$ draws, unit cost per instruction); the input and output layouts are in `PrivGaussMS.GoalLayout`; TV is the published `tvDist`.
--
--   Differences from the source:
--   - reading: 'For a sufficiently large universal constant c, it suffices to use n = ⌈c[…]⌉' → ∃ c > 0 and the guarantee for every n ≥ ⌈c·F⌉; reason: every larger constant also suffices, so the admissible n are all integers ≥ ⌈c₀F⌉ (planning decision 3)
--   - reading: 'There is an (ε, δ)-DP mechanism M … The mechanism uses O(n³) operations' → one admissible program of the published PolySampIso real RAM for all d, m, n, α, δ, ε, which receives them as input; every run halts within A·n³ executed instructions on every dataset and every tape, A universal; reason: the paper names no machine; Algorithm 2 computes its parameters (33) from public inputs, and a program per instance would make the cost clause vacuous; the paper's bound is worst case (p.54)
--   - encoding: a mechanism taking n records and releasing m vectors → fixed input cells for d, m, n, α, δ, ε and the records, fixed output cells read at the first halting step; reason: a machine needs a layout; no instance changes
--   - encoding: the mechanism's output law → the pushforward of the tape measure, with joint measurability of the output map asserted as a clause and IsDPM asserting probability laws; reason: a non-measurable map would be pushed to the zero measure, making DP vacuous
--   - encoding: L(M(X)) = Q_P^{⊗m} including input and mechanism randomness → equality of the pushforward of N(µ, Σ)^{⊗n} ⊗ tape with the product of Q_P; reason: Definition 1.2's law
--   - encoding: TV → the published tvDist (sup over measurable sets); reason: same definition (p.23)
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Theorem B.1, pp.31–32, eqs. (10)–(11) (explicit form of Theorem 1.1, p.3)

import Mathlib
import Definitions.Def_PrivGaussMS_GoalLayout
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-- **Theorem B.1** (Private Gaussian sampling with independent outputs), Moayedi, Yassaee,
Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256
1838c582…), pp.31–32 (explicit form of Theorem 1.1, p.3).

There are constants `c, A > 0` and one admissible program `P` of the published `PolySampIso` real
RAM such that for all integers `d, m ≥ 1`, all `0 < α, δ < 1`, `0 < ε ≤ 1` and every
`n ≥ ⌈c[mL + (d + L)(√(mL) + L)/ε]⌉`, `L = 1 + log(dm/(αδε))` (11), the mechanism `x ↦ P(x)`
taking `n` records of `ℝ^d` and releasing `m` vectors of `ℝ^d`:
1. halts on every dataset and every tape within `A n³` executed instructions;
2. has a jointly measurable output map;
3. is `(ε, δ)`-differentially private over all datasets;
4. on `X ∼ P^{⊗n}`, `P = N(µ, Σ)`, `Σ ≻ 0`, releases exactly `Q_P^{⊗m}`, `Q_P = (1 − η)P + ηN(0, I_d)`,
   `η = α/(2m)` (10), including input and mechanism randomness;
5. and `TV(Q_P^{⊗m}, P^{⊗m}) ≤ α/2`.

**Formalization Note.** "For a sufficiently large universal constant `c`, it suffices to use
`n = ⌈c·F⌉`" is read as `∃ c > 0` with every `n ≥ ⌈c·F⌉` (every `c' ≥ c` gives every larger
integer). "There is a mechanism" is one program for all parameters, which receives
`d, m, n, α, δ, ε` and the records as input (`goalInput`); "`O(n³)` operations" is the worst-case
count of executed instructions of that program, on every dataset and every tape. The input and
output layouts are in `Def_PrivGaussMS_GoalLayout`. -/
theorem theorem_B_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧ ∃ P : PolySampIso.Program, PolySampIso.Admissible P ∧
      ∀ d m : ℕ, 1 ≤ d → 1 ≤ m → ∀ α δ ε : ℝ, 0 < α → α < 1 → 0 < δ → δ < 1 → 0 < ε → ε ≤ 1 →
      ∀ n : ℕ,
        let L : ℝ := 1 + Real.log ((d : ℝ) * m / (α * δ * ε))
        ⌈c * ((m : ℝ) * L + ((d : ℝ) + L) * (Real.sqrt ((m : ℝ) * L) + L) / ε)⌉₊ ≤ n →
        (∀ (x : Fin n → Vec d) (ω : PolySampIso.Streams), ∃ t : ℕ,
            (PolySampIso.run P (goalInput d m n α δ ε x) ω t).halted = true ∧
            ((PolySampIso.run P (goalInput d m n α δ ε x) ω t).work : ℝ) ≤ A * (n : ℝ) ^ 3) ∧
        Measurable (goalOutput P d m n α δ ε) ∧
        IsDPM (fun x : Fin n → Vec d =>
          PolySampIso.tape.map fun ω => goalOutput P d m n α δ ε (x, ω)) ε δ ∧
        (∀ (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ), Sig.PosDef →
          ((Measure.pi fun _ : Fin n => multivariateGaussian μ Sig).prod PolySampIso.tape).map
              (goalOutput P d m n α δ ε) =
            Measure.pi fun _ : Fin m => QP μ Sig (α / (2 * m))) ∧
        (∀ (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ), Sig.PosDef →
          FoundationsRL.DECLower.tvDist (Measure.pi fun _ : Fin m => QP μ Sig (α / (2 * m)))
            (Measure.pi fun _ : Fin m => multivariateGaussian μ Sig) ≤ α / 2) := by sorry

end PrivGaussMS
