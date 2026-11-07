-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_lemma_4_11
-- name    : QAdvFew.PoQOracle.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:10.168491+00:00
-- url     : https://prove2.me/theorems/c80cc0c2-e3ff-4aab-9e88-2eb85afa2e18
-- title:
--   Lemma 4.11 — $r$ salted majorities are hard for $\mathsf{AC}^0[\oplus]$
-- statement:
--   There is a universal constant $\beta>0$ such that, for all fixed $d$ and polynomials $p,q$: if $r\le p(n)$ and $\mathcal C$ is a distribution over $\mathsf{AC}^0[\oplus](2^{q(n)},d)$ circuits, then for all sufficiently large $n$,
--   $$\Pr_{C\leftarrow\mathcal C,\ \mathrm{RO},\ x_1,\dots,x_r\leftarrow\{0,1\}^n}[C(x_1,\dots,x_r,\mathrm{RO})=H^{\mathrm{RO}}_r(x_1,\dots,x_r)]\le e^{-\beta r}.$$
--
--   This combines Theorem 3.11 with the direct-product theorem, for circuits reading the random oracle.
--
--   Differences from the source:
--   - reading: for all sufficiently large n → n₀ depending only on d, p, q, with the bound for all n ≥ n₀, r ≤ p(n) and 𝒞; reason: constants are fixed before the quantified objects; the proof's collision and size terms are uniform in r ≤ p(n)
--   - encoding: a distribution over circuits → a PMF on circuits with inputs the bits of the x_i and the strings naming RO positions, independent of RO and the x_i; reason: circuits form a countable set
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 4.11, p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_IsAC0Xor
import Definitions.Def_QAdvFew_PoQOracle_HMaj
import Definitions.Def_QAdvFew_PoQOracle_roInput
import Definitions.Def_QAdvFew_PoQOracle_roMeasure

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Lemma 4.11** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*,
arXiv:2611.05303v1, Lemma 4.11, p. 26 (PDF p. 28)). There is a universal constant `β > 0` such that,
for all fixed `d` and polynomials `p, q`: if `r ≤ p(n)` and `𝒞` is a distribution over
`AC0[⊕](2^{q(n)}, d)` circuits, then for all sufficiently large `n`,
`Pr_{C←𝒞, RO, x₁,…,x_r←{0,1}^n}[C(x₁, …, x_r, RO) = H^{RO}_r(x₁, …, x_r)] ≤ e^{−βr}`.

**Formalization Note** "For all sufficiently large `n`" is uniform: `n₀` depends on `d, p, q` only,
and the bound holds for every `n ≥ n₀`, every `r ≤ p(n)` and every `𝒞`. The circuits read the bits
`x_i[k]` and the random oracle (input `s` carrying `RO_{|s|}(s)`), with `r` outputs; `𝒞` is a
probability mass function on circuits, independent of `RO` and the `x_i`. -/
theorem lemma_4_11 : ∃ β : ℝ, 0 < β ∧ ∀ (d : ℕ) (p q : Polynomial ℕ), ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → ∀ r : ℕ, r ≤ p.eval n →
    ∀ 𝒞 : PMF (Circuit (Fin r × Fin n ⊕ List Bool)),
      (∀ C ∈ 𝒞.support, IsAC0Xor C ((2 : ℝ) ^ q.eval n) d) →
      ∑' C, 𝒞 C * (roMeasure.prod (PMF.uniformOfFintype (Fin r → Fin n → Bool)).toMeasure)
          {z | C.eval (fun _ => false) (Sum.elim (fun ik => z.2 ik.1 ik.2) (roInput z.1 ⊤)) =
            List.ofFn (HMaj (fun t u => z.1 ⟨t, u⟩) z.2)} ≤
        ENNReal.ofReal (Real.exp (-(β * r))) := by sorry

end QAdvFew.PoQOracle
