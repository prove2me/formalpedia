-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_mixedMeanCounterexample
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.mixedMeanCounterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:23:02.695677+00:00
-- url     : https://prove2.me/theorems/00f5116c-cc19-41df-89a1-a211cf9ef0b3
-- title:
--   Mean-energy mixed-codeword counterexample
-- statement:
--   Let $N_S>0$. Let the channel be either thermal noise with $0<\eta\le1$ and $N_B\ge0$, or additive noise with $v\ge0$. A mean constraint requires total expected photons at most $nN_S$ for each message separately. Write $A(P)=g(\eta P+(1-\eta)N_B)-g((1-\eta)N_B)$ in the thermal case and $A(P)=g(P+v)-g(v)$ in the additive case. All codes use the full countable Fock space and actual finite POVMs. Let $B=g(\eta N_S+(1-\eta)N_B)-\log_2(1+2(1-\eta)N_B)$ for the thermal channel, and $B=g(N_S+v)-\log_2(1+2v)$ for the additive channel. There exist $P>N_S$, a fixed rate $B<R<A(P)$, reliable coherent codebooks $|\alpha^n(m)\rangle$ of energy at most $nP$, their decoders, and errors $\epsilon_n\to0$ bounding every message error. Put $p=1-N_S/P$ and dilute each word by vacuum. The resulting actual family has the same decoder, eventual rate at least $R$, and
--
--   $$\rho_m=(1-p)|\alpha^n(m)\rangle\langle\alpha^n(m)|+p|0\rangle\langle0|^{\otimes n},\qquad\Pr(\widehat m=m\mid m)\ge\frac{N_S}{P}(1-\epsilon_n).$$
--
--   Every diluted codeword satisfies the mean constraint, and average success does not tend to zero. This constructs the failure of the strong converse under a mean constraint, including the reliable high-energy code family as part of the conclusion.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 8, §4.1, (24)–(28)

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

/-- Section 4.1, PDF pp.8–9, (24)–(28). Constructs both the reliable coherent
family and its diluted family. P and the strict rate are chosen in the conclusion.
NS>0 and nonzero signal transmissivity exclude vacuum/replacer degeneracies.
Coherent codewords have energy at most nP; literal iid draws do not all have
exact energy nP. The same decoder is used for the actual mixed codewords. -/
theorem mixedMeanCounterexample (C : ChannelSpec) (hC : ValidChannel C)
    (hsignal : match C with | .thermal eta _ => 0 < eta | .additive _ => True)
    (NS : ℝ) (hNS : 0 < NS) :
    ∃ P R : ℝ, NS < P ∧ giovannettiRateBound C NS < R ∧ R < coherentCodeRateBits C P ∧
      ∃ (M : ℕ → ℕ) (F G : (n : ℕ) → FockCommunicationCode n (M n))
        (alpha : (n : ℕ) → Fin (M n) → Fin n → ℂ) (epsilon : ℕ → ℝ),
        ReliableCoherent C P F alpha epsilon ∧
        (∀ᶠ n in atTop, R ≤ communicationRateBits n (M n)) ∧
        (∀ n, 0 < n →
          MeanConstraint NS (G n) ∧ (G n).decoder = (F n).decoder ∧
          ∀ m, ((G n).encoder m).coefficients = mixedWord (alpha n m) (1 - NS / P) ∧
            (NS / P) * (1 - epsilon n) ≤ messageSuccess C (G n) m) ∧
        ¬ Tendsto (fun n => decodingSuccessProbability C (G n)) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
