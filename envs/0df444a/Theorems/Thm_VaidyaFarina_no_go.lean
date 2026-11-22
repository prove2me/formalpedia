-- Prove2me | Theorems.Thm_VaidyaFarina_no_go
-- name    : VaidyaFarina.no_go
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:54:46.662341+00:00
-- url     : https://prove2.me/theorems/736194f9-99fa-49a4-b1de-e41c78fb8fd5
-- title:
--   No-go: Galilean mechanics cannot host the full Maxwell system
-- statement:
--   **Main no-go theorem (the paper's conclusion).** There is no field-independent transformation law for the charge and current sources that makes the full Maxwell system covariant under the Galilean boost forced by the Feynman–Dyson setup. Concretely, there do not exist maps $R(\rho,j,v)$ and $J(\rho,j,v)$ — functions of the source values and the boost velocity $v$ alone, not of the fields — such that for every solution $(E,H,\rho,j)$ of the full Maxwell system, the boosted fields $E'=E+v\times H,\ H'=H$ together with the transformed sources $\rho'=R(\rho,j,v),\ j'=J(\rho,j,v)$ (evaluated at the corresponding spacetime point) again satisfy the full Maxwell system. This is the precise sense in which "full Maxwell equations and Galilean mechanics are incompatible" (Vaidya–Farina, p. 266).
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 266, conclusion after eq. (19)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem no_go :
  ¬ ∃ (R : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
      (J : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
    ∀ (E H : ST → (Fin 3 → ℝ)) (rho : ST → ℝ) (j : ST → (Fin 3 → ℝ)) (v : Fin 3 → ℝ),
      FullMaxwell E H rho j →
      FullMaxwell (boostE v E H) (boostH v H)
        (fun p => R (rho (p.1 + p.2 • v, p.2)) (j (p.1 + p.2 • v, p.2)) v)
        (fun p => J (rho (p.1 + p.2 • v, p.2)) (j (p.1 + p.2 • v, p.2)) v) := by sorry
end VaidyaFarina
