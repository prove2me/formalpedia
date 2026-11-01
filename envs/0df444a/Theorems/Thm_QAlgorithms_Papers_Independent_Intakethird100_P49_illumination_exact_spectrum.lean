-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_illumination_exact_spectrum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.illumination_exact_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:43:30.305644+00:00
-- url     : https://prove2.me/theorems/54aabdac-dda4-4a01-979c-b66d563f260a
-- title:
--   Supplement III.B, Eqs.(146)–(149): exact illumination spectrum with source corrections
-- statement:
--   Let $d\ge1$ be the number of single-photon modes, $D=d+1$, $0\le b$, $db\le1$, and $0\le\eta\le1$. With one photon total plus vacuum, set $\tau_b=(1-db)|0\rangle\langle0|+bI_{\rm one}$, $\mathcal E_0(X)=\operatorname{tr}(X)\tau_b$, and $\mathcal E_1=(1-\eta)\mathcal E_0+\eta\,\mathrm{id}$. These are CPTP. For their normalized Choi states $\sigma,\rho$, put $\Omega^2=\sqrt\sigma\rho\sqrt\sigma$ and $a=1-db$. Its spectrum, including multiplicity, consists of
--
--   $$d^2\text{ copies of }\frac{(1-\eta)b^2}{D^2},\quad d\text{ copies of }\frac{(1-\eta)a^2}{D^2},\quad\operatorname{spec}(C/D^2),$$
--
--   where $C_{00}=(1-\eta)a^2+\eta a$, $C_{0k}=C_{k0}=\eta\sqrt{ab}$, $C_{kk}=(1-\eta)b^2+\eta b$ for $k>0$, and $C_{jk}=\eta b$ for distinct positive $j,k$. Thus $F(\sigma,\rho)=\sum_{\lambda\in\operatorname{spec}(\Omega^2)}\sqrt\lambda$. The factors $1-\eta$ omitted in the printed spectrum and lower-block diagonal are restored from exact Eq. (148), pending independent correction review. This retains an exact finite illumination calculation without relying on the subsequent expansion.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 17, Supplement III.B, Eqs.(146)–(149): exact illumination spectrum with source corrections

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P49

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond AdaptiveTest adaptiveInput adaptiveAccept)

open QAlgorithms.Papers.Independent.Bridge50.P25
  (LOCCOn normalizedChannelChoi TwoWayGenerationCode TwoWayChannelProtocol
   generationCodeError twoWayGenerationCapacity sendChannelRegister StateFunctional
   IsDimensionChangingLOCCMonotone privateStateInPartyOrder)

open QAlgorithms.Papers.Independent.Support50.P07 (amplitudeDampingChannel)

/-- Supplement III.B, PDF p.17, (146)--(149): exact illumination spectrum.
Printed d^2-fold eigenvalue b^2/D^2 is changed to (1-eta)*b^2/D^2;
printed lower-block diagonal is changed as documented in illuminationBlock.
Both corrections are forced by exact (148); independent moderation is required.
Eigenvalues are a multiset, so coincidences and zero eigenvalues keep multiplicity. -/
theorem illumination_exact_spectrum (d : ℕ) (hd : 1 ≤ d) (b eta : ℝ)
    (hb : 0 ≤ b) (hdb : (d : ℝ)*b ≤ 1) (heta : eta ∈ Set.Icc 0 1) :
    IsChannel (illuminationChannel d b 0) ∧ IsChannel (illuminationChannel d b eta) ∧
    (List.ofFn (ascEigenvalues (illuminationOmegaSquared d b eta))).Perm
      (List.replicate (d*d) ((1-eta)*b^2/((d : ℝ)+1)^2) ++
       List.replicate d ((1-eta)*(1-d*b)^2/((d : ℝ)+1)^2) ++
       List.ofFn (ascEigenvalues (illuminationBlock d b eta))) ∧
    rootFidelity (normalizedChannelChoi (illuminationChannel d b 0))
      (normalizedChannelChoi (illuminationChannel d b eta)) =
      ∑ i, Real.sqrt (ascEigenvalues (illuminationOmegaSquared d b eta) i) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
