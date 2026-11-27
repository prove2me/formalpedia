-- Prove2me | Theorems.Thm_RelaxedIndexability_Supplement_theorem_ec_1
-- name    : RelaxedIndexability.Supplement.theorem_ec_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:06:02.731813+00:00
-- url     : https://prove2.me/theorems/2a69f24b-5583-4325-bc5b-51466b885ac9
-- title:
--   Theorem EC.1 (corrected: cases 1.3, 1.5, 1.12, 1.17, 2.1 and the a′ = 0 boundary) — the first crossing time of a three-state arm in closed form
-- statement:
--   Let $\mathbf P$ be an irreducible and aperiodic $3\times3$ transition matrix and $B\in\mathbb R^3$ a reward vector. Fix beliefs $\omega$ and $\omega^*$, let $r^*=\omega^*B'$, let $h(k)=\omega\mathbf P^kB'$ be the $k$-step reward function, and let
--   $$
--   L(\omega,\omega^*)=\min\{k\ge0:\ h(k)>r^*\}\quad(+\infty\text{ if there is no such }k)
--   $$
--   be the first crossing time. Then:
--
--   1. (EC.46) $L=0$ if $h(0)>r^*$; $L=1$ if $h(1)>r^*\ge h(0)$; $L=2$ if $h(2)>r^*\ge\max\{h(0),h(1)\}$;
--   2. for every representation $h(k)=a_1b_1^k+a_2b_2^k+c$ with $|b_1|,|b_2|<1$, the cases 1.1–1.22 hold, and they hold also with the indices $1$ and $2$ exchanged; every parameter tuple satisfies the hypothesis of one of the cases 1.1–1.22, directly or after the exchange (case 1.23);
--   3. for every representation $h(k)=ab^k+ckb^{k-1}+d$ with $|b|<1$, the cases 2.1–2.5 hold;
--   4. for every representation $h(k)=a'A^k\sin(k\theta+b')+c'$ with $A\in(0,1)$, $a'\ge0$, $\theta\in(0,2\pi)$ and $b'\in[0,2\pi)$: when $a'>0$, cases 3.1–3.8 hold with $d'=(r^*-c')/a'$; when $a'=0$, $h(k)=c'$ is constant and $L=0$ if $r^*<c'$, while $L=+\infty$ if $c'\le r^*$.
--
--   The cases are those of `crossingTable`, as printed except for five false entries, which are replaced by the values that the paper's proof gives. In 1.3 and 1.5 the finite branch is $\lfloor\log_{b}\frac{c-r^*}{-a}\rfloor+1$. In 1.12 the base is $|b_1|/b_2$ and the even floor replaces the floor. In 1.17 the odd floor replaces the floor. In 2.1, $h(\lceil z_3\rceil)$ replaces $h(z_3+1)$. For example, in case 2.1, $\mathbf P$ with rows $(\frac23,\frac16,\frac16)$, $(\frac1{12},\frac{17}{24},\frac5{24})$, $(\frac14,\frac18,\frac58)$, $B=(0,7,17)$, $\omega=(0,1,0)$ and $\omega^*=(\frac{827}{1700},0,\frac{873}{1700})$ give $h(k)=-(\frac12)^k+k(\frac12)^{k-1}+8$, $z_3=\frac32$ and $r^*=8.73$. Then $L=2$, while $h(z_3+1)=h(\frac52)\approx8.707\le r^*$ makes the printed formula give $\infty$.
--
--   With $L$ known, the closed form (41) of the approximated Whittle index (the goal theorem) can be evaluated for three-state arms without simulating the passive orbit.
--
--   **Formalization Note** `crossTime P B ωstar ω` is $L(\omega,\omega^*)$, with the threshold as third argument. The statement holds for every representation, because the coefficients are not unique in degenerate cases. $a'>0$ is where $d'$ is defined. The explicit $a'=0$ branch completes the boundary case left out by the printed table; (EC.46) supplies $L=0$ when the constant sequence is above the threshold, and the definition of first crossing gives $L=+\infty$ otherwise.
--
--   Differences from the source:
--   - correction: case 1.3 (and 1.5) finite branch ⌊log_{b₂}((c−r*)/(−a₂))⌋ + 2 → ⌊log_{b₂}((c−r*)/(−a₂))⌋ + 1; reason: false as printed: P rows (7/12,1/12,1/3), (1/12,7/12,1/3), (1/3,1/3,1/3), B = (0,6,6), ω = (1,0,0), ω* = (1/2,1/2,0) give h = 0, 5/2, 13/4, …, r* = 3, L = 2, printed 3; the proof (p.ec18) says h increases for k ≥ 1
--   - correction: case 1.12 ⌊log_{b₁/b₂} z₁⌋ + 2 → ⌊log_{|b₁|/b₂} z₁⌋_e + 2 in the range and in both conditions; reason: false as printed: P rows (1/2,1/4,1/4), (1/4,1/8,5/8), (1/4,5/8,1/8), B = (0,40,56), ω = (1/2,0,1/2), ω* = (79/400,321/400,0) give L = 2 while the printed second branch (base repaired) gives ∞; the proof (p.ec20) uses maximum even integers
--   - correction: case 1.17 ⌊log_{−b₁/b₂} z₂⌋ + 2 → ⌊log_{−b₁/b₂} z₂⌋_o + 2 in the range and in both conditions; reason: false as printed: the same P, B = (0,88,104), ω = (1/2,1/2,0), ω* = (239/880,641/880,0) give L = 3 while the printed second branch gives ∞; the proof (p.ec21) uses maximum odd integers
--   - correction: case 2.1 h(z₃ + 1) → h(⌈z₃⌉) in both branches; reason: false as printed when z₃ is not an integer: P rows (2/3,1/6,1/6), (1/12,17/24,5/24), (1/4,1/8,5/8), B = (0,7,17), ω = (0,1,0), ω* = (827/1700,0,873/1700) give z₃ = 3/2, L = 2, while h(5/2) ≈ 8.707 ≤ r* = 8.73 makes the printed second branch give ∞; the proof (p.ec23) puts the maximum at the integer k₁ + 1 = ⌈z₃⌉
--   - correction: Lemma EC.1 allows a′ = 0, but cases 3.1–3.8 define d′ = (r*−c′)/a′ and give no value of L at that boundary → if a′ = 0, L = 0 when r* < c′ and L = +∞ when c′ ≤ r*; reason: the form in Lemma EC.1 is then the constant sequence h(k) = c′, so the strict first-crossing definition settles both branches
--   - reading: misprints 1.7 "r* ≥ h(0),h(1)", 1.13 base b₁/b₂ < 0, 1.19 "h(k) > ω*", 1.21 and 2.4 "{h(0),h(1),h(·)} ≤ r*", 1.22 "ω* ≥ h(1)", 3.7 and 3.8 "b" → both inequalities, base |b₁|/b₂, h(k) > r*, max{…} ≤ r*, r* ≥ h(1), b′; reason: each printed form is ill-formed or undefined, and the intended one is the only well-formed reading
--   - reading: 1.23 "any other case, which is symmetric to one of the above" and 2.5 "forms similar to those in (1.1)-(1.6)" → every tuple satisfies a hypothesis of 1.1–1.22 directly or after exchanging the indices, all cases also hold for the exchanged tuple; for c = 0 the forms of 1.5–1.6 with (a₁,b₁,c) := (a,b,d), for b = 0 the form of 1.4; reason: the exchange of (a₁,b₁) and (a₂,b₂) is the symmetry of h, and these are the forms the omitted details reduce to
--   - encoding: the parameters of each case → every representation of h in the form of Lemma EC.1; reason: the coefficients are not unique in degenerate cases and every one is covered
--   - encoding: P irreducible and aperiodic → Matrix.IsPrimitive P; reason: equivalent for a finite stochastic matrix (p.ec11)
--   - generalization: 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: the theorem does not use it; every B includes the source's case
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Theorem EC.1, (EC.46)–(EC.65), pp.ec13–ec17; proof pp.ec17–ec25

import Mathlib
import Definitions.Def_RelaxedIndexability_crossTime
import Definitions.Def_RelaxedIndexability_Supplement_kStepReward
import Definitions.Def_RelaxedIndexability_Supplement_crossingTable

open Matrix

namespace RelaxedIndexability.Supplement

/-- **Theorem EC.1, corrected** (Liu, arXiv:2107.11939v4, Theorem EC.1, pp.ec13–ec17). Let `K = 3`
and `P` be irreducible and aperiodic. Fix beliefs `ω` and `ω*`, let `r* = ω* B′` and
`h(k) = ω P^k B′`. Then the first crossing time `L(ω, ω*)` satisfies

* (EC.46) (`InitialCases`);
* for every representation `h(k) = a₁ b₁^k + a₂ b₂^k + c`, `|b₁|, |b₂| < 1`: cases 1.1–1.22
  (`DiagonalizableCases`), and case 1.23: the same cases with the indices exchanged, one of 1.1–1.22
  applying either directly or after the exchange (`IsListed`);
* for every representation `h(k) = a b^k + c k b^(k−1) + d`, `|b| < 1`: cases 2.1–2.5
  (`JordanCases`);
* for every representation `h(k) = a′ A^k sin(kθ + b′) + c′` in the ranges of Lemma EC.1 with
  `a′ > 0`: cases 3.1–3.8 (`ComplexCases`); if `a′ = 0`, then `h` is constant and `L = 0` when
  `r* < c′`, while `L = ∞` when `c′ ≤ r*`.

**Formalization Note.** `crossTime P B ωstar ω` is `L(ω, ω*)`, threshold first. The printed
theorem is false in cases 1.3, 1.5, 1.12, 1.17 and 2.1; the statement here takes the values that
the proof gives. `a′ > 0` is where `d′ = (r* − c′)/a′` is defined; the `a′ = 0` branch restores
the constant sequence allowed by Lemma EC.1 but omitted from the printed table. -/
theorem theorem_ec_1 (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin 3)) (hprim : P.IsPrimitive) (B : Fin 3 → ℝ)
    (ω : Fin 3 → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin 3))
    (ωstar : Fin 3 → ℝ) (hωstar : ωstar ∈ stdSimplex ℝ (Fin 3)) :
    InitialCases (kStepReward P B ω) (ωstar ⬝ᵥ B) (crossTime P B ωstar ω) ∧
    (∀ a₁ b₁ a₂ b₂ c : ℝ, IsDiagonalizableForm (kStepReward P B ω) a₁ b₁ a₂ b₂ c →
      DiagonalizableCases (kStepReward P B ω) (ωstar ⬝ᵥ B) (crossTime P B ωstar ω)
          a₁ b₁ a₂ b₂ c ∧
      DiagonalizableCases (kStepReward P B ω) (ωstar ⬝ᵥ B) (crossTime P B ωstar ω)
          a₂ b₂ a₁ b₁ c ∧
      (IsListed a₁ b₁ a₂ b₂ ∨ IsListed a₂ b₂ a₁ b₁)) ∧
    (∀ a b c d : ℝ, IsJordanForm (kStepReward P B ω) a b c d →
      JordanCases (kStepReward P B ω) (ωstar ⬝ᵥ B) (crossTime P B ωstar ω) a b c d) ∧
    (∀ a' A θ b' c' : ℝ, IsComplexForm (kStepReward P B ω) a' A θ b' c' →
      (0 < a' →
        ComplexCases (kStepReward P B ω) (ωstar ⬝ᵥ B) (crossTime P B ωstar ω)
            a' A θ b' c') ∧
      (a' = 0 →
        ((ωstar ⬝ᵥ B) < c' → crossTime P B ωstar ω = 0) ∧
        (c' ≤ (ωstar ⬝ᵥ B) → crossTime P B ωstar ω = ⊤))) := by sorry

end RelaxedIndexability.Supplement
