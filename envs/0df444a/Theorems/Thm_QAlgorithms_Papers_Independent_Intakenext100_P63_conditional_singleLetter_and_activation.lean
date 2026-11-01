-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_conditional_singleLetter_and_activation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.conditional_singleLetter_and_activation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:21:04.537539+00:00
-- url     : https://prove2.me/theorems/885a31bd-4493-43b9-905d-6d16a35a03c6
-- title:
--   Conditional single-letter and activated weak locking capacity formulas
-- statement:
--   Assume either the global constrained minimum-output Arimoto Renyi entropy additivity conjecture (16), for every pair of finite POVMs and normalized constraint states at every order $\alpha>1$, or the uniform IID smooth conditional min-entropy relation (17): for every finite normalized ensemble, $0<\varepsilon<1$, and slack $s>0$, eventually every collective POVM satisfies $H_{\min}^{\varepsilon}(I^n|J)\ge n(S_{\rm acc}(I|E)-s)$. All smoothing uses normalized states and half trace-norm distance.
--
--   For a channel $\mathcal N$ with a cq complementary channel in a fixed input basis,
--
--   $$L_W(\mathcal N)=\max_pS_{\rm acc}(I|E)=L_W^{(u)}(\mathcal N),$$
--
--   where $L_W^{(u)}(\mathcal N)=\max_{\{p_x,\rho_x\}}[\chi(\{p_x,\mathcal N(\rho_x)\})-I_{\rm acc}(\{p_x,\mathcal N^c(\rho_x)\})]$ optimizes every finite normalized mixed ensemble. Furthermore, for any finite-dimensional channel with its fixed normalized Stinespring dilation,
--
--   $$\overline L_W(\mathcal N):=\sup_{k\ge1}\{L_W(\mathcal N\otimes\mathrm{id}_k)-\log_2k\}=\sup_{n\ge1}\frac1nL_W^{(u)}(\mathcal N^{\otimes n})\ge L_W(\mathcal N).$$
--
--   All spaces are nonzero, rates are in bits, and ordinary locking capacity permits only a sublinear preshared independent uniform secret. Both conclusions retain the conjectural premise. The finite-ensemble maximum defining the upper information is attained. The activated formula charges for the noiseless factor and does not equate ordinary and activated capacities in general.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 15, Theorem 15: conditional single-letter and activated capacity formulas

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.14–15, Theorem 15: BOTH clauses retain the global conjectural premise.
Activated keyedCapacity is distinct from ordinary weak locking keyedCapacity. -/
theorem conditional_singleLetter_and_activation
    (hconj : ConstrainedRenyiAdditivity ∨ IIDUncertainty) :
    (∀ (a b e : ℕ), 0 < a → 0 < b → 0 < e →
      ∀ V : Matrix (Fin b × Fin e) (Fin a) ℂ, Vᴴ * V = 1 →
      ∀ rho : Fin a → Mat (Fin e), CqComplement (environment V) rho →
        keyedCapacity (dilationMap V) (environment V) true = optimizedEquivocation rho ∧
        optimizedEquivocation rho = upperInformation (dilationMap V) (environment V)) ∧
    (∀ (a b e : ℕ), 0 < a → 0 < b → 0 < e →
      ∀ V : Matrix (Fin b × Fin e) (Fin a) ℂ, Vᴴ * V = 1 →
        activatedCapacity (dilationMap V) (environment V) = regularizedUpper (dilationMap V) (environment V) ∧
        keyedCapacity (dilationMap V) (environment V) true ≤ activatedCapacity (dilationMap V) (environment V) ∧
        (∃ (m : ℕ) (p : Fin m → ℝ) (sigma : Fin m → Mat (Fin a)),
          IsDistribution p ∧ (∀ i, IsDensityMatrix (sigma i)) ∧
          upperInformation (dilationMap V) (environment V) =
            labelInformation p (fun i => dilationMap V (sigma i)) - shannon p +
              accessibleEquivocation p (fun i => environment V (sigma i)))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
