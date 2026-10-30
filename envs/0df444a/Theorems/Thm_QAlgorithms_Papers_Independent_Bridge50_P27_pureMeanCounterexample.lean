-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_pureMeanCounterexample
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.pureMeanCounterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:24:03.976236+00:00
-- url     : https://prove2.me/theorems/e1640f91-d67e-41c6-bf40-1d173f7fdd68
-- title:
--   Mean-energy pure-codeword counterexample with a noisy flag use
-- statement:
--   Let $N_S>0$. Let the channel be either thermal noise with $0<\eta\le1$ and $N_B\ge0$, or additive noise with $v\ge0$. A mean constraint requires total expected photons at most $nN_S$ for each message separately. Write $A(P)=g(\eta P+(1-\eta)N_B)-g((1-\eta)N_B)$ in the thermal case and $A(P)=g(P+v)-g(v)$ in the additive case. All codes use the full countable Fock space and actual finite POVMs. Set $B=g(\eta N_S/[(1-\eta)N_B+1])$ for thermal noise, and $B=g(N_S/(v+1))$ for additive noise. There exist $P>N_S$, a fixed $B<R<A(P)$, reliable coherent data codes of energy at most $nP$, their decoders, and errors $\epsilon_n\to0$. Eventually $nP-1>0$ and
--
--   $$p_n=\frac{nP-(n+1)N_S}{nP-1}\in[0,1],\qquad|\gamma_{p_n}(m)\rangle=\sqrt{1-p_n}|\alpha^n(m)\rangle|0\rangle+\sqrt{p_n}|0\rangle^{\otimes n}|1\rangle.$$
--
--   These are normalized pure codewords on $n+1$ physical noisy uses, each with mean energy per use at most $N_S$. The receiver discards the last output mode and uses the data decoder. Their actual rate $\log_2 M_n/(n+1)$ is eventually at least $R$, and
--
--   $$\Pr(\widehat m=m\mid m)\ge(1-p_n)(1-\epsilon_n).$$
--
--   Average success does not tend to zero. This constructs the pure-state counterexample while counting both the extra photon and extra noisy channel use.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 9, §4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P27

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

-- Exact accepted definitions, checked against their complete source bodies.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)

open QAlgorithms.Papers.Independent.Renew46.P30 (photonTotal)

open QAlgorithms.Papers.Independent.Support50.P06 (totalEnergy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 4.2, PDF p.9. Constructs pure codewords on n+1 NOISY uses.
The flag photon and denominator n+1 are counted. The eventual mixing probability
solves the displayed energy formula at energy nP; upper-bounded coherent energies
therefore satisfy the required per-codeword mean bound. The physical receiver
uses the data decoder tensored with identity on the last output mode. -/
theorem pureMeanCounterexample (C : ChannelSpec) (hC : ValidChannel C)
    (hsignal : match C with | .thermal eta _ => 0 < eta | .additive _ => True)
    (NS : ℝ) (hNS : 0 < NS) :
    ∃ P R : ℝ, NS < P ∧ lossBound C NS < R ∧ R < coherentCodeRateBits C P ∧
      ∃ (M : ℕ → ℕ) (F : (n : ℕ) → FockCommunicationCode n (M n))
        (G : (n : ℕ) → FockCommunicationCode (n + 1) (M n))
        (alpha : (n : ℕ) → Fin (M n) → Fin n → ℂ) (epsilon : ℕ → ℝ),
        ReliableCoherent C P F alpha epsilon ∧
        (∀ᶠ n in atTop, R ≤ communicationRateBits n (M n) ∧ R ≤ communicationRateBits (n + 1) (M n)) ∧
        (∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
          0 < (n : ℝ) * P - 1 ∧
          0 ≤ flagMixing NS P n ∧ flagMixing NS P n ≤ 1 ∧
          MeanConstraint NS (G n) ∧ PureEncoding (G n) ∧
          ∀ m, ((G n).encoder m).coefficients = flaggedWord (alpha n m) (flagMixing NS P n) ∧
            (G n).decoder.effect m = discardFlagPOVM (F n).decoder m ∧
            (1 - flagMixing NS P n) * (1 - epsilon n) ≤ messageSuccess C (G n) m) ∧
        ¬ Tendsto (fun n => decodingSuccessProbability C (G n)) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
