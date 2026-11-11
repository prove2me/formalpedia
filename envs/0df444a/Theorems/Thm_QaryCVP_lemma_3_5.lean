-- Prove2me | Theorems.Thm_QaryCVP_lemma_3_5
-- name    : QaryCVP.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:04.118629+00:00
-- url     : https://prove2.me/theorems/1422832f-1d3c-4880-bb55-87ee084a3059
-- title:
--   Lemma 3.5 — exact search $E_\tau$ in a ball, in time $2^{(ab_\tau+n\ln\Theta(a))/(2\ln2)+O(\sqrt n\log(n+2))}$
-- statement:
--   Fix a rational $\tau\in[0,1]$. There are deterministic programs $E$ (for $E_\tau$) and $E'$ (for the variant $E^{\ne0}_\tau$) such that, for integers $n\ge1$, $m\ge0$, $q\ge2$ and inputs $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$, $y\in\mathbb Q^n$, $b\in\mathbb Q_{\ge0}$:
--
--   1. $E$ returns a vector of minimum distance from $y$ in $\{x\in\mathbb Z^n: Hx=0_m,\ \|x-y\|^2\le b\}$, or $\bot$ exactly when this set is empty; $E'$ does the same for the nonzero solutions.
--   2. With $f=\lfloor y\rceil-y$: if $b<\|f\|^2$, both return $\bot$ in polynomial time.
--   3. With $b_\tau=b-\tau\|f\|^2$: for $b=O(n)$ and any $a=a(n)>0$ with $a=\Omega(1)$, $a=O(\log(n+2))$ satisfying (10), $\Theta_u(a)\le\Theta(a)e^{-a\tau u^2}$ for $|u|\le1/2$, every execution uses
--
--   $$\text{time } 2^{\frac{ab_\tau+n\ln\Theta(a)}{2\ln2}+O(\sqrt n\log(n+2))},\qquad\text{space } 2^{\frac{ab_\tau+n\ln\Theta(a)}{4\ln2}+O(\sqrt n\log(n+2))},$$
--
--   omitting factors polynomial in the binary input length.
--
--   This is the exact step of the $\gamma$-CVP algorithm: it finds the closest point when the target is near the lattice and certifies a lower bound on the distance otherwise.
--
--   **Formalization Note** $b=O(n)$, $a=\Omega(1)$, $a=O(\log(n+2))$ are $b\le Dn$, $a_0\le a\le A_1\log_2(n+2)$ for arbitrary fixed $D,a_0,A_1>0$; the $O(\sqrt n\log(n+2))$ constant $C_1$ and the polynomial degree are chosen after them and before the input.
--
--   Differences from the source:
--   - reading: the procedure (a specific algorithm of the paper) → there is a program of the RAM with every stated property, bundled for the same program; reason: decision 3: writing the algorithm as RAM code inside a statement is not feasible; the bundle carries every property later steps use
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: the paper's cost model; this machine charges bit operations at least as heavily (decision 1)
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13: poly is a polynomial in the binary input length
--   - reading: on every input and execution → the run halts on every coin tape and the bounds hold on every tape; reason: p.13, Theorem 1.1
--   - encoding: deterministic procedure → the program's run is the same on every coin tape; reason: determinism on the randomized machine
--   - reading: b = O(n), a = Ω(1), a = O(log(n+2)), and O(√n log(n+2)) in the exponent → b ≤ Dn and a₀ ≤ a ≤ A₁ log₂(n+2) for arbitrary D, a₀, A₁ > 0, with the error constant C₁ and degree K chosen after them; reason: p.12 asymptotic conventions; the program is chosen before D, a₀, A₁
--   - generalization: correctness for inputs b = O(n) → correctness for every b ≥ 0; reason: the correctness argument (§3.2.1, p.28) does not use b = O(n); specializes to the lemma
--   - encoding: ⊥ → the empty output word; reason: n ≥ 1 makes it distinct from every vector
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 3.5, p.28; Definition 3.4, p.24; (10), p.28; (48), p.62

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- **Lemma 3.5** (exact search inside a prescribed ball), for `E_τ` and its nonzero variant
`E^{≠0}_τ`. Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4),
Lemma 3.5, p.28; Definition 3.4, p.24; (10), p.28; (48), p.62.

Fix a rational `τ ∈ [0, 1]`. There are deterministic programs `E` and `E'` such that, for integers
`n ≥ 1`, `m ≥ 0`, `q ≥ 2` and inputs `H ∈ (Z/qZ)^{m×n}`, `y ∈ Qⁿ`, `b ∈ Q≥0`:

1. `E` returns a vector of minimum distance from `y` in `{x ∈ Zⁿ : Hx = 0_m, ‖x − y‖² ≤ b}`, or `⊥`
   exactly when this set is empty; `E'` does the same for the nonzero solutions;
2. with `f = ⌊y⌉ − y`, if `b < ‖f‖²` both return `⊥` in polynomial time;
3. with `b_τ = b − τ‖f‖²`, for `b = O(n)` and any `a = a(n) > 0` with `a = Ω(1)` and
   `a = O(log(n + 2))` satisfying (10), `Θ_u(a) ≤ Θ(a)e^{−aτu²}` for `|u| ≤ 1/2`, every execution uses
   bit time `2^{(ab_τ + n ln Θ(a))/(2 ln 2) + O(√n log(n+2))}` and bit space
   `2^{(ab_τ + n ln Θ(a))/(4 ln 2) + O(√n log(n+2))}`, omitting polynomial factors in the binary input
   length.

**Formalization Note.** Decision 3 (existential form). Deterministic = the run is the same on every
coin tape. `b = O(n)`, `a = Ω(1)`, `a = O(log(n+2))` are `b ≤ Dn`, `a₀ ≤ a ≤ A₁ log₂(n+2)` for
arbitrary fixed `D, a₀, A₁ > 0`, and the `O(√n log(n+2))` constant `C₁` and the polynomial degree are
chosen after them and before the input. The output word is empty for `⊥`. Clause 1 is stated for every
`b ≥ 0` (the correctness argument, p.28, does not use `b = O(n)`). -/
theorem lemma_3_5 (τ : ℚ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ∃ E E' : Program,
      (∀ n m q : ℕ, 1 ≤ n → 2 ≤ q →
        ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ) (b : ℚ), 0 ≤ b →
          DetOn E (encSearch H y b) ∧ DetOn E' (encSearch H y b) ∧
          (∀ ω : ℕ → Bool, ∃ o : Option (Fin n → ℤ), IsSearchOutput (fun _ => True) H y b o ∧
            callOutput E (Config.init (encSearch H y b)) ω = some (optWord o)) ∧
          (∀ ω : ℕ → Bool, ∃ o : Option (Fin n → ℤ), IsSearchOutput (fun x => x ≠ 0) H y b o ∧
            callOutput E' (Config.init (encSearch H y b)) ω = some (optWord o))) ∧
      (∃ K : ℕ, ∀ n m q : ℕ, 1 ≤ n → 2 ≤ q →
        ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ) (b : ℚ), 0 ≤ b →
          b < sqDist (roundVec y) y →
          TimeWithin E (encSearch H y b) (polyF K (encSearch H y b)) ∧
          TimeWithin E' (encSearch H y b) (polyF K (encSearch H y b))) ∧
      (∀ D a₀ A₁ : ℝ, 0 < D → 0 < a₀ → 0 < A₁ →
        ∃ (C₁ : ℝ) (K : ℕ), ∀ n m q : ℕ, 1 ≤ n → 2 ≤ q →
          ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ) (b : ℚ), 0 ≤ b →
            (b : ℝ) ≤ D * n → sqDist (roundVec y) y ≤ b →
            ∀ a : ℝ, a₀ ≤ a → a ≤ A₁ * Real.logb 2 (n + 2) → ThetaCond τ a →
              let e : ℝ := a * ((b : ℝ) - τ * sqDist (roundVec y) y) + n * Real.log (theta a)
              let err : ℝ := C₁ * Real.sqrt n * Real.logb 2 (n + 2)
              RunsWithin E (encSearch H y b)
                ((2 : ℝ) ^ (e / (2 * Real.log 2) + err) * polyF K (encSearch H y b))
                ((2 : ℝ) ^ (e / (4 * Real.log 2) + err) * polyF K (encSearch H y b)) ∧
              RunsWithin E' (encSearch H y b)
                ((2 : ℝ) ^ (e / (2 * Real.log 2) + err) * polyF K (encSearch H y b))
                ((2 : ℝ) ^ (e / (4 * Real.log 2) + err) * polyF K (encSearch H y b))) := by sorry

end QaryCVP
