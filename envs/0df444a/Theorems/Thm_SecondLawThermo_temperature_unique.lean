-- Prove2me | Theorems.Thm_SecondLawThermo_temperature_unique
-- name    : SecondLawThermo.temperature_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-15T21:16:13.157285+00:00
-- url     : https://prove2.me/theorems/42eb2577-b813-4f8d-bf68-d5ca943a2954
-- title:
--   Uniqueness of the absolute temperature scale at fixed reference
-- statement:
--   Source-faithful helper for the thermodynamic temperature scale: any two everywhere-positive temperature scales that agree at the reference reservoir T0 and both reproduce every Carnot heat ratio must be equal. Uses only Carnot existence and field algebra.
-- source:
--   mission:cfeb14ae-5258-474a-b322-a36986b26451:parent:79732920-55bf-49dd-87f8-bc20491793e2:E150-declaration

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

open SecondLawThermo

theorem SecondLawThermo.temperature_unique {Θ : Type*} [LinearOrder Θ]
    (𝒞 : Set (SecondLawThermo.Cycle Θ)) (hCarnot : SecondLawThermo.CarnotEnginesExist 𝒞)
    (T₀ : Θ) (T T' : Θ → ℝ)
    (hTpos : ∀ t, 0 < T t) (hT₀ : T T₀ = 273.16)
    (hTcorr : ∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → SecondLawThermo.IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = T k / T h)
    (hT'pos : ∀ t, 0 < T' t) (hT'₀ : T' T₀ = 273.16)
    (hT'corr : ∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → SecondLawThermo.IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = T' k / T' h) :
    T' = T := by sorry
