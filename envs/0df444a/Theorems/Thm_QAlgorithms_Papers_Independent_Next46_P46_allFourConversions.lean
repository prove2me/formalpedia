-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_allFourConversions
-- name    : QAlgorithms.Papers.Independent.Next46.P46.allFourConversions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:58:29.241841+00:00
-- url     : https://prove2.me/theorems/53378644-60ee-4e8a-a24a-06ebc6e772b6
-- title:
--   Coherent information is achievable in all four resource conversions
-- statement:
--   Let all registers be finite dimensional. In the static setting, let $|\psi\rangle^{ABE}$ be any unit purification of the supplied state $\rho^{AB}$. In the dynamic setting, independently choose an isometry $U:A'\to BE$ and a unit preparation $|\psi'\rangle^{AA'}$ on Alice's side; now $\rho^{AB}$ is the marginal after one application of $U$. Eve receives the entire complementary output. Write $R=H(B)-H(AB)$, with entropy in bits.
--
--   In each setting the corresponding private and quantum conversions attain the coherent-information lower bound:
--
--   $$
--   \frac{\log_2 M}{n}\ge R-\delta.
--   $$
--
--   Precisely, for every $\varepsilon,\delta>0$, every sufficiently large positive blocklength $n$ admits a protocol with this yield and full trace-norm error at most $\varepsilon$ from a uniform shared secret key, or an $M$-dimensional EPR state, respectively. The target is independent of Eve. Static protocols use only local operations and forward public messages, copied to Eve. Dynamic protocols use $n$ independent channel uses and no auxiliary communication. Only the supplied source is initially shared.
--
--   This is an achievable-rate assertion; it does not identify the optimal capacities. For $R\le0$ it imposes no positive-yield requirement.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 4, Conclusion; scenarios 1–4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF pp.1--4: all four resource conversions.
Static source quantification and dynamic channel/input quantification are separate.
Nonpositive coherent information is interpreted as a lower bound on nonnegative yield. -/
theorem allFourConversions :
    (∀ {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
      [Nonempty A] [Nonempty B] [Nonempty E]
      (psi : Vec (A × (B × E))), IsState psi →
      let rho := pureDensity psi
      StaticPrivateAchievable rho (coherentInfo (marginalAB rho)) ∧
      StaticQuantumAchievable psi (coherentInfo (marginalAB rho))) ∧
    (∀ {A P B E : Type} [Fintype A] [Fintype P] [Fintype B] [Fintype E]
      [Nonempty A] [Nonempty P] [Nonempty B] [Nonempty E]
      (U : Matrix (B × E) P ℂ), IsDilation U →
      ∀ psi : Vec (A × P), IsState psi →
      let rho := pureDensity (channelSource U psi)
      DynamicPrivateAchievable U (coherentInfo (marginalAB rho)) ∧
      DynamicQuantumAchievable U (coherentInfo (marginalAB rho))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
