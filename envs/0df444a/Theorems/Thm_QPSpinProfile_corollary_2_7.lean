-- Prove2me | Theorems.Thm_QPSpinProfile_corollary_2_7
-- name    : QPSpinProfile.corollary_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:50.181644+00:00
-- url     : https://prove2.me/theorems/32eb5706-ff4b-4150-9109-a877b3c8d788
-- title:
--   Corollary 2.7: quadratic profile complexity
-- statement:
--   Fix $p\ge2$ and let $\mathcal C_n$ be a class of $n$-qubit states. Suppose there are sequences $a_n,b_n\ge0$ and $B_n\ge1$ such that for every $0<\varepsilon\le1$
--   $$
--   \log N(\varepsilon,F_{n,p}(\mathcal C_n),\|\cdot\|_{n,p})\le a_n+b_n\log(B_n/\varepsilon),
--   $$
--   and that for some $A>0$
--   $$
--   \limsup_{n\to\infty}\frac{a_n+b_n\log(eB_nn)}{n^2}\le A .
--   $$
--   Then, with a universal constant $C$, for every fixed $0<\alpha<1/2$, writing $K=C\big[2^{p/2}p^{3/2}\sqrt A/\sqrt\alpha+3^{p/2}\sqrt{p\alpha}\big]$,
--   $$
--   \limsup_{n\to\infty}\frac{\mathbb E\,\Delta^{\mathrm{ref}}_{n,p}(\mathcal C_n;\mathrm{prod}_n)}{\sqrt n}\le K ,
--   $$
--   and for every $\varepsilon>0$, with probability tending to one,
--   $$
--   E_{n,p}(\mathcal C_n)\le E_{n,p}(\mathrm{prod}_n)+(K+\varepsilon)\sqrt n .
--   $$
--
--   This is the quantitative estimate that, combined with the ground-state benchmark, yields Theorem 1.2(i).
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: standing assumption (p.3): all state classes are nonempty → explicit hypotheses that each class is nonempty and consists of density operators; reason: the paper's standing assumption made explicit; it also keeps the real suprema $E_{n,p}$ meaningful
--   - reading: the constant $C$, written without a quantifier → one universal constant chosen before $p$, the class, the sequences, $A$ and $\alpha$; reason: the displayed bound already carries the explicit dependence on $p$, $\alpha$, $A$; the proof's constants (Lemma 2.6, Corollary 2.4) are universal; this is the stronger reading
--   - encoding: $\log N\le a_n+b_n\log(B_n/\varepsilon)$ → $N$ finite and $\log N\le a_n+b_n\log(B_n/\varepsilon)$, assumed for $n\ge p$; reason: an infinite $N$ makes the printed bound false; for $n<p$ there are no weight-$p$ strings, $N=1$ and the bound holds automatically
--   - encoding: $\limsup_n x_n\le y$ → for every $\delta>0$, eventually $x_n\le y+\delta$; reason: the definition of the lim sup, avoiding Mathlib's junk value of `limsup` on unbounded real sequences
--   - encoding: $\mathbb E\,\Delta^{\mathrm{ref}}/\sqrt n$ → lower Lebesgue integral of $\Delta^{\mathrm{ref}}/\sqrt n$; reason: the integrand is nonnegative; no integrability condition is hidden
--   - encoding: $2^{p/2}$, $3^{p/2}$, $\log(eB_nn)$ → $(\sqrt2)^p$, $(\sqrt3)^p$, `Real.log (exp 1 * B n * n)`; reason: equal
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Corollary 2.7, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QPSpinProfile_profile
import Definitions.Def_QPSpinProfile_coverNum
import Definitions.Def_QPSpinProfile_prodStatesOn
import Definitions.Def_QPSpinProfile_maxEnergy

namespace QPSpinProfile

open MeasureTheory Filter Topology

/-- **Corollary 2.7 (Quadratic profile complexity)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.25, PDF p.28).
Fix `p ≥ 2` and classes `C_n`. If `a_n, b_n ≥ 0`, `B_n ≥ 1` satisfy
`log N(ε, F_{n,p}(C_n), ‖·‖_{n,p}) ≤ a_n + b_n log(B_n/ε)` for every `0 < ε ≤ 1` and
`lim sup_n (a_n + b_n log(e B_n n))/n² ≤ A` for some `A > 0`, then for every fixed
`0 < α < 1/2`, with `K := C[2^{p/2} p^{3/2} √A/√α + 3^{p/2} √(pα)]`:
`lim sup_n E Δ^ref_{n,p}(C_n; prod_n)/√n ≤ K`, and for every `ε > 0`, with probability tending
to one, `E_{n,p}(C_n) ≤ E_{n,p}(prod_n) + (K + ε)√n`.

**Formalization Note** `C` is universal (quantified before `p`, the classes, `A` and `α`).
"`log N ≤ …`" is "`N` finite and `log N ≤ …`", assumed for `n ≥ p` (for `n < p` there are no
weight-`p` strings, `N = 1` and the bound holds automatically). `lim sup_n x_n ≤ y` is
`∀ δ > 0, eventually x_n ≤ y + δ`, never Mathlib's real `limsup`. The expectation of the
nonnegative `Δ^ref/√n` is a lower Lebesgue integral. Classes are nonempty sets of states. -/
theorem corollary_2_7 : ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ) (Cl : (n : ℕ) → Set (Matrix (Qubits n) (Qubits n) ℂ)) (a b B : ℕ → ℝ) (A : ℝ),
      2 ≤ p → (∀ n, (Cl n).Nonempty) → (∀ n, ∀ ρ ∈ Cl n, WildeQIT.IsDensityOperator ρ) →
      (∀ n, 0 ≤ a n) → (∀ n, 0 ≤ b n) → (∀ n, 1 ≤ B n) →
      (∀ n : ℕ, p ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        coverNum ε (profileClass n p (Cl n)) ≠ ⊤ ∧
        Real.log ((coverNum ε (profileClass n p (Cl n))).toNat : ℝ) ≤ a n + b n * Real.log (B n / ε)) →
      0 < A →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        (a n + b n * Real.log (Real.exp 1 * B n * n)) / (n : ℝ) ^ 2 ≤ A + δ) →
      ∀ α : ℝ, 0 < α → α < 1 / 2 →
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
          ∫⁻ g, ENNReal.ofReal (deltaRef n p (Cl n) (prodStates n) g / Real.sqrt n) ∂(gaussMeasure n p)
            ≤ ENNReal.ofReal (C * (Real.sqrt 2 ^ p * (p : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt A / Real.sqrt α
                + Real.sqrt 3 ^ p * Real.sqrt ((p : ℝ) * α)) + δ)) ∧
        (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => gaussMeasure n p
          {g | maxEnergy n p (Cl n) g ≤ maxEnergy n p (prodStates n) g +
            (C * (Real.sqrt 2 ^ p * (p : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt A / Real.sqrt α
                + Real.sqrt 3 ^ p * Real.sqrt ((p : ℝ) * α)) + ε) * Real.sqrt n}) atTop (𝓝 1)) := by sorry

end QPSpinProfile
