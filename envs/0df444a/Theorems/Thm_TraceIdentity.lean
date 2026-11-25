-- Prove2me | Theorems.Thm_TraceIdentity
-- name    : TraceIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:06:49.000807+00:00
-- url     : https://prove2.me/theorems/f250adff-5e12-4c13-bb1e-412345b783ce
-- title:
--   Trace Identity: Trace Identity
-- statement:
--   The paper's eq:trace: evaluating `E_p(u) = 0` at the maximum point `e` and
--   summing the deficits over an orthonormal basis of `e`-perp.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TraceIdentity.lean#L11-L89
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TraceIdentity.lean#L11-L89

module
public import Definitions.Def_PHarmonicPoly_MaxPointDerivatives
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_TraceIdentity
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_MaxPointDerivatives

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem TraceIdentity {n m : ℕ} (hm : 1 ≤ m) {p : ℝ} {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m) {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1)
    (hE : EpAlg p P = 0)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {i₀ : Fin n} (hb0 : b i₀ = e) :
    ∑ i ∈ Finset.univ.erase i₀,
        (iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
            ![b i, b i] + (m : ℝ) * ((m : ℝ) - 1))
      = ((n : ℝ) - p) * ((m : ℝ) * ((m : ℝ) - 1)) := by sorry
