-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P01_path_instrument
-- name    : QAlgorithms.Papers.Independent.Claimed50.P01.path_instrument
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:29:23.894041+00:00
-- url     : https://prove2.me/theorems/a3c43205-1c75-4a1c-a259-7c8427fd3b65
-- title:
--   Sequential path instrument equals the coherent Schur block, including conditional retained state
-- statement:
--   Let $d\ge2$, $n\ge1$, and fix one coherent family of one-qudit CG unitary intertwiners. Let $p$ be any valid full path through the Young lattice, ending in $\lambda\vdash_d n$. Independently construct $U^{\mathrm{Sch}}_n$ by the unmeasured super-CG recursion, and let $B_p$ be its row block for the single multiplicity copy indexed by $p$. Let $K_p$ be the sequential product of measured local CG blocks. Then
--
--   $$
--   K_p=B_p,\qquad K_p X K_p^\dagger=B_p X B_p^\dagger
--   $$
--
--   for every input operator $X$ on the $n$ received systems. Removing zero-padded output rows identifies $B_p$ with $\Pi_{\lambda,p}^{\mathrm{Sch}}U_n^{\mathrm{Sch}}$.
--
--   More generally, for $r\ge0$ and any density operator $\rho$ on $n+r$ arrivals, put $\rho_{[n]}=\operatorname{Tr}_{\mathrm{unread}}\rho$ and $\Omega_p=(K_p\otimes I)\rho(K_p^\dagger\otimes I)$. Then
--
--   $$
--   \operatorname{Tr}_{\mathrm{unread}}\Omega_p=B_p\rho_{[n]}B_p^\dagger.
--   $$
--
--   Write $w_p=\operatorname{Tr}(K_p\rho_{[n]}K_p^\dagger)$. If $w_p=0$, the full subnormalized branch $\Omega_p$ is zero. If $w_p>0$, both $\Omega_p/w_p$ and $K_p\rho_{[n]}K_p^\dagger/w_p$ are density operators, and
--
--   $$
--   \operatorname{Tr}_{\mathrm{unread}}\frac{\Omega_p}{w_p}
--   =\frac{B_p\rho_{[n]}B_p^\dagger}{w_p}.
--   $$
--
--   Thus the path identity specifies the entire retained irrep state, including its correlations with unread inputs, rather than only the final Young-label probability. This result concerns defining-register Schur sampling; it does not assert a dual-register or mixed-Schur theorem.
-- source:
--   Weak Schur sampling with logarithmic quantum memory, arXiv:2309.11947v1, PDF p. 9, III, Eqs.(23),(34)-(44)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P01

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P01

attribute [local instance] Classical.propDecidable

/-- Eqs.(23),(34)-(44): equality of the sequential CP instrument with each
coherent Schur block, together with its positive-probability conditional
retained state and partial-trace readout (PDF pp.7-9). The induction uses the
previous label in the latest CG factor, correcting the type mismatch in the
printed Eqs.(42)-(44). This is the defining-register algorithm of this paper;
no dual-register or mixed-Schur extension is asserted. -/
theorem path_instrument {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (C : CGSystem d) (p : Path d n) :
    sequentialKraus C n p.val = schurBlock C p ∧
    (∀ rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ,
      sequentialBranch C p rho = schurBlock C p * rho * (schurBlock C p)ᴴ) ∧
    (∀ (r : ℕ) (rho : Matrix ((Fin (n + r) → Fin d)) ((Fin (n + r) → Fin d)) ℂ),
      IsDensityMatrix rho →
      traceUnread (paddedBranch C p rho) =
        schurBlock C p * prefixDensity n r rho * (schurBlock C p)ᴴ ∧
      (pathProbability C p (prefixDensity n r rho) = 0 → paddedBranch C p rho = 0) ∧
      (0 < pathProbability C p (prefixDensity n r rho) →
        let weight : ℂ := (pathProbability C p (prefixDensity n r rho) : ℂ)⁻¹
        IsDensityMatrix (weight • paddedBranch C p rho) ∧
        IsDensityMatrix (weight • sequentialBranch C p (prefixDensity n r rho)) ∧
        traceUnread (weight • paddedBranch C p rho) =
          weight • (schurBlock C p * prefixDensity n r rho * (schurBlock C p)ᴴ))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P01

end
