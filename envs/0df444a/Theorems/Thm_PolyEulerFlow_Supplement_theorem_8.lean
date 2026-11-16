-- Prove2me | Theorems.Thm_PolyEulerFlow_Supplement_theorem_8
-- name    : PolyEulerFlow.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:07:28.316994+00:00
-- url     : https://prove2.me/theorems/a0b5776a-a9a7-4e65-bbf0-f3ff5b21cdf5
-- title:
--   Theorem 8 — P is unit-step and mesh-uniform polynomial-time decision by a rational polynomial field
-- statement:
--   Let $d\in\mathbb N$ and $L\subseteq\mathbb N^d$. The following are equivalent.
--
--   1. $L\in\mathsf P$.
--   2. Some scale-controlled rational polynomial system decides $L$ **at unit step** ($\eta=1$) with a polynomial threshold $S$ and a polynomial horizon $Q$, its exact orbits staying in a fixed compact box: for every $x$ and every $s\ge S(\ell(x))$, with $h=2^{-s}$, the orbit $z_0=c(x,h)$, $z_{k+1}=z_k+F(x,h,z_k)$ stays in the box and $|z_k(o)-1_L(x)|\le1/4$ for all $k\ge Q(s)$.
--   3. Some such system decides $L$ **mesh-uniformly**: one threshold $S$, horizon $Q$, box and output coordinate $o$ work for every step $\eta\in(0,1]$, the output being correct for all $k\ge\lceil Q(s)/\eta\rceil$.
--
--   Moreover, for $L\in\mathsf P$ there is a witness of item 3 whose active length up to the decision horizon is polynomial in $s$, uniformly in $\eta$: there is a polynomial $\Lambda$ with
--   $$\mathrm{Len}_\eta\big(z;\lceil Q(s)/\eta\rceil\big)=\sum_{k<\lceil Q(s)/\eta\rceil}\|z_{k+1}-z_k\|_\infty\le\Lambda(s)$$
--   for every $\eta\in(0,1]$, every $x$ and every $s\ge S(\ell(x))$.
--
--   Polynomial time is thus exactly what a compact rational polynomial dynamics decides in polynomial physical time, and the characterization is the same for every Euler step.
--
--   **Formalization Note** The conclusion is $(1\Leftrightarrow2)\wedge(1\Leftrightarrow3)\wedge(1\Rightarrow$ item 3 with the length bound$)$. The dimension $m$ of the system is existential.
--
--   Differences from the source:
--   - encoding: integer polynomials for the scale threshold S and the physical time Q → polynomials with natural coefficients; reason: every integer polynomial is dominated by one with natural coefficients, and correctness is required at every larger scale and every later index, so both existentials are equivalent
--   - encoding: L ∈ P for L ⊆ ℕ^d (inputs in binary) → a polynomial-time Mathlib multi-stack machine on the self-delimiting encoding encodeNatVec (length Σ(2ℓ(x_i)+2)); reason: standard binary input of linear length for fixed d; the published PvsNP machine model
--   - encoding: a fixed compact box → a coordinatewise box [lo, hi] with real corners; reason: every compact set lies in such a box, which is itself compact
--   - reading: the construction in Item 3 has active length polynomial in s on the prefix up to the decision horizon, uniformly in η → for L ∈ P there is an Item-3 witness and a polynomial Λ with Len_η(z; ⌈Q(s)/η⌉) ≤ Λ(s) for all η ∈ (0,1], x and s ≥ S(ℓ(x)); reason: the construction is not a named object; the claim about it is the existence of such a witness
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 8, pp.6–7 (PDF 8–9); Definitions 3, 4, 7, pp.5–6; proof p.33 (PDF 35)

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_ScaleSystem

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- **Theorem 8 (Polynomial time)**, pp.6–7 (PDF 8–9). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…): "For every language L ⊆ ℕ^d, the following are equivalent. 1. L ∈ P. 2. L is decided by a unit-step scale-controlled
rational polynomial field with polynomial scale threshold and polynomial physical time, while all active variables remain in a fixed compact
box. 3. L is decided mesh-uniformly by such a field, with the same scale threshold, physical time, compact box and output coordinate for every
η ∈ (0, 1]. The construction in Item 3 has active length polynomial in s on the prefix up to the decision horizon, uniformly in η."

The conclusion is `(1 ⇔ 2) ∧ (1 ⇔ 3) ∧ (1 ⇒ a witness of 3 with active length Len_η(z; ⌈Q(s)/η⌉) ≤ Λ(s))`.

**Formalization Note.** A system is a `ScaleSystem d m` (Definition 3) with `m` existential; the threshold `S` and the horizon `Q` are
polynomials with natural coefficients (dominating an integer polynomial changes neither item, since correctness is required for every larger
scale and every later index); the box is `[lo, hi]`; `L ∈ P` is polynomial time on the self-delimiting binary encoding `encodeNatVec`. -/
theorem theorem_8 {d : ℕ} (L : Set (Fin d → ℕ)) :
    (InP L ↔ ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr Q : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ),
        S.StablyDecidesAt L Sthr Q o lo hi 1) ∧
    (InP L ↔ ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr Q : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ),
        ∀ η : ℝ, 0 < η → η ≤ 1 → S.StablyDecidesAt L Sthr Q o lo hi η) ∧
    (InP L → ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr Q Λ : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ),
        (∀ η : ℝ, 0 < η → η ≤ 1 → S.StablyDecidesAt L Sthr Q o lo hi η) ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (x : Fin d → ℕ) (s : ℕ), Sthr.eval (vecLength x) ≤ s →
          activeLengthOn (S.orbit x s η (fun _ => 0)) 0 ⌈((Q.eval s : ℕ) : ℝ) / η⌉₊ ≤ ((Λ.eval s : ℕ) : ℝ)) := by sorry

end PolyEulerFlow.Supplement
