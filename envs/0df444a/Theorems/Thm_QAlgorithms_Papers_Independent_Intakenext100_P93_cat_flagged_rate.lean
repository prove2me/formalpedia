-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P93_cat_flagged_rate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P93.cat_flagged_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:36:11.139782+00:00
-- url     : https://prove2.me/theorems/cc8741e6-e531-4300-80af-5589393afc89
-- title:
--   Equation (5): flagged coherent information and achievable concatenated-cat rate
-- statement:
--   Let $p_x,p_y,p_z\ge0$ with sum at most one, and fix the positive cat length $m=k+1$. Encode half of the normalized Bell state $\Phi^+=|\phi^+\rangle\langle\phi^+|$, apply the independent physical Pauli channel, decode, and measure and retain the complete syndrome. Denote this actual instrument output by $\omega_{ABS}$, the syndrome mass by $P(s)=\sum_{u,v}J(u,v,s)$, and its conditional logical channel by $\mathcal N^s$. Each conditional channel is the Pauli mixture with weights $J(u,v,s)/P(s)$ when $P(s)>0$; at zero mass choose the identity. The output is a density matrix and
--
--   $$
--   \omega_{ABS}=\sum_s P(s)(\operatorname{id}\otimes\mathcal N^s)(\Phi^+)\otimes|s\rangle\langle s|,
--   $$
--   $$
--   R_m=\frac{I^c(\omega_{ABS})}{m}
--   =\frac1m\sum_sP(s)I^c((\operatorname{id}\otimes\mathcal N^s)(\Phi^+))
--   =\frac{1+H(S)-H(U,V,S)}m.
--   $$
--
--   Here $I^c(\rho_{AB})=S(\rho_B)-S(\rho_{AB})$, the receiver includes the syndrome, and every entropy uses base two. If $R_m\ge0$, this rate is achievable by this fixed cat inner encoder concatenated with outer additive stabilizer encoders: for every fidelity error $\epsilon>0$ and rate slack $\delta>0$, every sufficiently large positive outer length $n$ admits an encoder for $l\ge(R_m-\delta)mn$ logical qubits and a CPTP decoder with entanglement fidelity and every normalized pure-input transmission fidelity at least $1-\epsilon$.
--
--   The operational assertion supplies high-fidelity unassisted quantum communication, rather than only an entropic number. Negative values remain signed expressions. At $m=1$ the expression is the Bell-input hashing yield, without input optimization.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, PDF p. 2, Equation (5): flagged coherent information and achievable concatenated-cat rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Smolin, PDF p.2, Eq.(5): actual flagged output, Pauli conditional
channels, coherent-information identity and operational random-stabilizer
concatenation rate. A negative signed expression is not an operational rate. -/
theorem cat_flagged_rate (k : ℕ) (px py pz : ℝ)
    (hx : 0 ≤ px) (hy : 0 ≤ py) (hz : 0 ≤ pz) (hsum : px + py + pz ≤ 1) :
    IsDensityMatrix (catInstrumentOutput k px py pz) ∧
    (∀ s : Qubits k, IsChannel (conditionalChannel k px py pz s) ∧
      ∀ rho : Matrix Bool Bool ℂ,
        conditionalChannel k px py pz s rho =
          ∑ u : Bool, ∑ v : Bool,
            ((if iidCatSyndromeMass k px py pz s = 0 then
              (if u = false ∧ v = false then 1 else 0)
            else catLogicalSyndromeMass k px py pz u v s / iidCatSyndromeMass k px py pz s : ℝ) : ℂ) •
              conjSuperop ((Stabilizer.pauliOfBits u v).mat) rho) ∧
    (∀ x y : Bool × (Bool × Qubits k), catInstrumentOutput k px py pz x y =
      if x.2.2 = y.2.2 then
        (iidCatSyndromeMass k px py pz x.2.2 : ℂ) *
          idTensorSuperop (R := Bool) (conditionalChannel k px py pz x.2.2)
            (pureDensity catBellInput) (x.1, x.2.1) (y.1, y.2.1)
      else 0) ∧
    catRate k px py pz =
      (∑ s : Qubits k, iidCatSyndromeMass k px py pz s *
        (let rho := idTensorSuperop (R := Bool) (conditionalChannel k px py pz s)
          (pureDensity catBellInput)
         vnEntropy (traceLeft rho) - vnEntropy rho)) / (k + 1 : ℕ) ∧
    catRate k px py pz =
      (1 + QAlgorithms.Papers.Independent.Support50.P40.finiteEntropyBits (iidCatSyndromeMass k px py pz) -
        QAlgorithms.Papers.Independent.Support50.P40.finiteEntropyBits (fun z : Bool × Bool × Qubits k =>
          catLogicalSyndromeMass k px py pz z.1 z.2.1 z.2.2)) / (k + 1 : ℕ) ∧
    (0 ≤ catRate k px py pz → CatAchievable k px py pz (catRate k px py pz)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P93

end
