-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_teleportation_dense_coding_conversions
-- name    : QAlgorithms.Papers.Independent.Support50.P11.teleportation_dense_coding_conversions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:19:15.451247+00:00
-- url     : https://prove2.me/theorems/11c995d4-0ad2-4958-a9a9-55938852497b
-- title:
--   Appendix B (B5)–(B8): exact fidelity-preserving teleportation and dense coding
-- statement:
--   Let $d\ge1$. Use the explicitly defined Weyl Bell measurement, one shared normalized Bell state and controlled Weyl corrections to define the EA teleportation and dense-coding codes. Let $P$ be input/output dephasing followed by permutation averaging, and $U$ the Haar twirl with inverse output conjugation. Define $T_d(M)=U\circ T\circ P[M]$ and $D_d(N)=P\circ D\circ U[N]$ by the actual CPTP constructions. Let $C^{(\lambda)}$ be the $d^2$-ary symmetric classical channel and $X^{(\lambda)}$ the isotropic $d$-dimensional channel parameterized by entanglement fidelity. For $\lambda\in[0,1]$, with $\lambda=1$ when $d=1$,
--   $$T_d(C^{(\lambda)})=X^{(\lambda)},\qquad D_d(X^{(\lambda)})=C^{(\lambda)}.$$
--   For every CPTP $M$ on $d^2$ dimensions and $N$ on $d$ dimensions, the converted maps are CPTP and admit actual EA-code realizations, and
--   $$T_d(M)=X^{(P_s(M))},\quad F(T_d(M))=P_s(M),\quad D_d(N)=C^{(F(N))},\quad P_s(D_d(N))=F(N).$$
--   This retains the exact endpoint fidelities and explicitly repairs the printed twirls.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 14, Appendix B (B5)–(B8): exact fidelity-preserving teleportation and dense coding

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.14--15, (B5)--(B8): actual Bell-protocol CPTP conversions, exact
optimalCodeFidelity preservation, and realization in EA. Corrected B1 includes dephasing;
corrected B2 uses inverse output conjugation via accepted haarTwirl. -/
theorem teleportation_dense_coding_conversions
    (d : ℕ) (hd : 0 < d) :
    IsForwardCode d .EA (teleportCode d hd) ∧ IsForwardCode (d * d) .EA (denseCode d hd) ∧
    (∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 → (d = 1 → lambda = 1) →
      teleportConversion d hd (symmetricClassical (d * d) lambda) = fidelityDepolarizing d lambda ∧
      denseConversion d hd (fidelityDepolarizing d lambda) = symmetricClassical (d * d) lambda) ∧
    (∀ M : Superop (Fin (d * d)) (Fin (d * d)), IsChannel M →
      IsChannel (teleportConversion d hd M) ∧
      teleportConversion d hd M = fidelityDepolarizing d (uniformClassicalSuccess M) ∧
      channelFidelity d (teleportConversion d hd M) = uniformClassicalSuccess M ∧
      ∃ Z : Superop (Fin d × Fin (d * d)) (Fin (d * d) × Fin d),
        IsForwardCode d .EA Z ∧ link d M Z = teleportConversion d hd M) ∧
    (∀ N : Superop (Fin d) (Fin d), IsChannel N →
      IsChannel (denseConversion d hd N) ∧
      denseConversion d hd N = symmetricClassical (d * d) (channelFidelity d N) ∧
      uniformClassicalSuccess (denseConversion d hd N) = channelFidelity d N ∧
      ∃ Z : Superop (Fin (d * d) × Fin d) (Fin d × Fin (d * d)),
        IsForwardCode (d * d) .EA Z ∧ link (d * d) N Z = denseConversion d hd N) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
